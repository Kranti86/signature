"""
Signature Journeys – E-sign app for Credit Card Authorization + Invoice

Flow:
  1. Admin creates a request (service, detailed description, amount, dates).
  2. Customer opens the link, reads disclosures, fills details, draws or types signature.
  3. Signed Authorization Form + signed Invoice PDFs are generated and stored.
  4. Admin records fulfillment status/date; downloads an evidence packet for the processor.

Environment variables:
  ADMIN_KEY    (required) long random secret for admin pages, min 16 characters
  STORAGE_DIR  (optional) folder for records/PDFs, e.g. /var/data on Render's disk
  FLASK_DEBUG  (optional) set to 1 only for local testing
"""
import base64, hashlib, io, json, os, re, secrets
from datetime import datetime, timezone
from pathlib import Path
from xml.sax.saxutils import escape

from flask import Flask, request, render_template_string, abort, send_file, url_for, redirect
from pypdf import PdfWriter
from reportlab.lib import colors
from reportlab.lib.pagesizes import letter
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.units import inch
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, Image
from werkzeug.middleware.proxy_fix import ProxyFix

# ======================================================================
# Configuration
# ======================================================================
BASE = Path(__file__).parent
STORAGE = Path(os.environ.get("STORAGE_DIR", BASE))
DATA_DIR = STORAGE / "data"
PDF_DIR = STORAGE / "signed_pdfs"
DATA_DIR.mkdir(parents=True, exist_ok=True)
PDF_DIR.mkdir(parents=True, exist_ok=True)

ADMIN_KEY = os.environ.get("ADMIN_KEY", "")
if len(ADMIN_KEY) < 16:
    raise RuntimeError("Set the ADMIN_KEY environment variable (at least 16 characters).")

app = Flask(__name__)
app.wsgi_app = ProxyFix(app.wsgi_app, x_proto=1, x_host=1)  # generate https:// links behind Render's proxy
app.config["MAX_CONTENT_LENGTH"] = 2 * 1024 * 1024  # 2 MB

COMPANY = {
    "name": "Signature Journeys LLC",
    "address": "3400 Cottage Way, Ste G2 #36935, Sacramento, CA 95825, US",
    "phone": "888 678 8890",
    "email": "Contact@signaturejourneys.info",
}
COMPANY_LINE = f"{COMPANY['name']} · {COMPANY['address']} · {COMPANY['phone']} · {COMPANY['email']}"

SERVICES = {
    "consultation": ("Trip Planning Consultation", "150.00"),
    "itinerary": ("Custom Itinerary Design", "200.00"),
    "concierge": ("Travel Concierge Support", "250.00"),
    "other": ("Other", ""),
}
STATUSES = ["Not started", "In progress", "Fulfilled"]

DISCLOSURE = [
    "Signature Journeys LLC does not sell, issue or book flights, hotels or car rentals.",
    "We are not an affiliate of any airline, hotel, car rental company, tour operator or other travel supplier.",
    "We are not a party to any agreement between you and a third-party travel provider. "
    "Those purchases are governed solely by the provider's terms and policies.",
    "We do not receive commissions from providers for the travel you book on your own.",
    "We cannot guarantee availability, prices, schedules or changes made by third-party providers, "
    "and we are not responsible for their cancellations, delays or refunds.",
    "Our fee covers planning and advisory services only. It does not include the cost of any travel product.",
]
REFUND_POLICY = (
    "Consultation fees are refundable in full if you cancel at least 48 hours before the session. "
    "Itinerary and concierge fees are refundable before work begins; once work has started, the fee "
    "is refundable only for the portion not yet delivered. Refunds are returned to the original card "
    "within 5–10 business days."
)
AUTH_TEXT = (
    "I, the cardholder named above, authorize Signature Journeys LLC to charge the amount shown in "
    "Section 3 to my card. I confirm that I am the authorized holder of this card and that I have read "
    "the Service Fees & Customer Disclosure. I understand that this charge is for planning and advisory "
    "services only and does not include the cost of any flight, hotel, car rental or other third-party "
    "travel product, which I will purchase directly from the provider. I understand the cancellation "
    "and refund policy and agree to its terms."
)
INVOICE_ACCEPT_TEXT = (
    "I agree to purchase the services described above at the price shown, under the terms, "
    "disclosures and refund policy stated in this invoice and the Credit Card Authorization Form."
)


def now_utc():
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")


def norm_name(s):
    return " ".join((s or "").split()).lower()


# ======================================================================
# Storage
# ======================================================================
def load(token):
    if not re.fullmatch(r"[A-Za-z0-9_-]{20,64}", token or ""):
        abort(404)
    path = DATA_DIR / f"{token}.json"
    if not path.exists():
        abort(404)
    return json.loads(path.read_text())


def save(token, record):
    (DATA_DIR / f"{token}.json").write_text(json.dumps(record, indent=2))


def require_admin():
    if not secrets.compare_digest(request.args.get("key", ""), ADMIN_KEY):
        abort(403)


# ======================================================================
# Validation
# ======================================================================
def luhn_ok(number):
    digits = [int(d) for d in number][::-1]
    return (sum(digits[0::2]) + sum(sum(divmod(2 * d, 10)) for d in digits[1::2])) % 10 == 0


def validate_customer(f):
    errors = []
    labels = {"full_name": "Full name", "address": "Billing address", "city_state_zip": "City, state, ZIP",
              "phone": "Phone", "email": "Email", "card_number": "Card number",
              "expiry": "Expiration date", "printed_name": "Printed name"}
    for key, label in labels.items():
        if not f.get(key, "").strip():
            errors.append(f"{label} is required.")

    if f.get("email") and not re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", f["email"].strip()):
        errors.append("Please enter a valid email address.")

    num = re.sub(r"\D", "", f.get("card_number", ""))
    if num and (not 13 <= len(num) <= 19 or not luhn_ok(num)):
        errors.append("Card number does not appear to be valid.")

    exp = f.get("expiry", "").strip()
    m = re.fullmatch(r"(0[1-9]|1[0-2])/(\d{2})", exp)
    if exp and not m:
        errors.append("Expiration date must be in MM/YY format.")
    elif m:
        now = datetime.now()
        if (2000 + int(m.group(2)), int(m.group(1))) < (now.year, now.month):
            errors.append("This card has expired.")

    if f.get("agree") != "yes":
        errors.append("You must confirm you have read the disclosures and authorize the charge.")

    method = f.get("sig_method", "drawn")
    if method not in ("drawn", "typed"):
        errors.append("Invalid signature method.")
    elif method == "typed":
        typed = norm_name(f.get("typed_name"))
        if not typed:
            errors.append("Please type your name as your signature.")
        elif typed != norm_name(f.get("printed_name")):
            errors.append("Your typed signature must match your printed name exactly.")

    if not f.get("signature", "").startswith("data:image/png;base64,"):
        errors.append("Please draw or type your signature.")
    return errors, num


def validate_request(f):
    errors = []
    key = f.get("service", "")
    if key not in SERVICES:
        return ["Choose a service."], None
    name, default_fee = SERVICES[key]
    if key == "other":
        name = f.get("custom_name", "").strip()
        if not name:
            errors.append("Enter the service name for 'Other'.")
    if len(f.get("description", "").strip()) < 30:
        errors.append("Please write a detailed description (at least 30 characters).")
    amount = f.get("amount", "").strip() or default_fee
    try:
        if float(amount) <= 0:
            raise ValueError
        amount = f"{float(amount):.2f}"
    except ValueError:
        errors.append("Enter a valid amount.")
    for k, label in (("charge_date", "Date of charge"), ("service_date", "Scheduled service date")):
        if not f.get(k):
            errors.append(f"{label} is required.")
    if f.get("status") not in STATUSES:
        errors.append("Choose a fulfillment status.")
    return errors, (name, amount)


# ======================================================================
# PDF building
# ======================================================================
_ss = getSampleStyleSheet()
TITLE = _ss["Title"]
BODY = ParagraphStyle("body", parent=_ss["Normal"], fontSize=10, leading=13)
SMALL = ParagraphStyle("small", parent=_ss["Normal"], fontSize=8.5, leading=11)
H2 = ParagraphStyle("h2", parent=_ss["Heading2"], fontSize=12, spaceBefore=10, spaceAfter=4)


def esc(text):
    return escape(str(text or "")).replace("\n", "<br/>")


def kv_table(rows):
    t = Table([[Paragraph(f"<b>{esc(k)}</b>", BODY), Paragraph(esc(v), BODY)] for k, v in rows],
              colWidths=[2.4 * inch, 4.6 * inch])
    t.setStyle(TableStyle([("GRID", (0, 0), (-1, -1), 0.5, colors.grey),
                           ("BACKGROUND", (0, 0), (0, -1), colors.whitesmoke),
                           ("VALIGN", (0, 0), (-1, -1), "TOP")]))
    return t


def grid_table(rows, widths):
    t = Table(rows, colWidths=widths, repeatRows=1)
    t.setStyle(TableStyle([("GRID", (0, 0), (-1, -1), 0.5, colors.grey),
                           ("BACKGROUND", (0, 0), (-1, 0), colors.lightgrey),
                           ("VALIGN", (0, 0), (-1, -1), "TOP")]))
    return t


def build_pdf(target, story):
    SimpleDocTemplate(target, pagesize=letter, leftMargin=0.75 * inch, rightMargin=0.75 * inch,
                      topMargin=0.6 * inch, bottomMargin=0.6 * inch).build(story)


def header(title):
    return [Paragraph(title, TITLE), Paragraph(esc(COMPANY_LINE), SMALL), Spacer(1, 8)]


def bill_to_rows(c):
    return [("Cardholder full name", c["full_name"]), ("Billing address", c["address"]),
            ("City, state, ZIP", c["city_state_zip"]), ("Phone number", c["phone"]),
            ("Email address", c["email"])]


def signature_block(r, sig_png):
    img = Image(io.BytesIO(sig_png), width=2.8 * inch, height=1.0 * inch, kind="proportional")
    img.hAlign = "LEFT"
    return [Paragraph("<b>Cardholder signature:</b>", BODY), img,
            kv_table([("Printed name", r["customer"]["printed_name"]),
                      ("Date signed", r["audit"]["signed_at_utc"])])]


def esign_record(r):
    a = r["audit"]
    if a.get("signature_method") == "typed":
        method = (f"Typed name (“{esc(a.get('typed_name'))}”) adopted by the signer "
                  "as their electronic signature")
    else:
        method = "Drawn by hand on screen"
    return [Paragraph("Electronic Signature Record", H2),
            Paragraph(f"Invoice / reference: {esc(r['service']['invoice_no'])}<br/>"
                      f"Signed: {esc(a['signed_at_utc'])}<br/>"
                      f"Signature method: {method}<br/>"
                      f"Signer email: {esc(r['customer']['email'])}<br/>"
                      f"Browser: {esc(a['user_agent'][:150])}<br/>"
                      "The signer agreed to sign electronically and confirmed reading the "
                      "Service Fees &amp; Customer Disclosure before signing.", SMALL)]


def authorization_story(r, sig_png):
    c, s = r["customer"], r["service"]
    return [
        *header("Signature Journeys – Credit Card Authorization Form"),
        Paragraph("By signing below, you authorize Signature Journeys LLC to charge the card listed on this "
                  "form for the travel consulting and concierge service fees described here. Signature "
                  "Journeys does not sell flights, hotels or car rentals and is not a party to any agreement "
                  "with third-party travel providers.", BODY),
        Paragraph("1. Cardholder Information", H2), kv_table(bill_to_rows(c)),
        Paragraph("2. Card Information", H2),
        kv_table([("Card type", c["card_type"]), ("Card number", f"**** **** **** {c['card_last4']}"),
                  ("Expiration date (MM/YY)", c["expiry"]),
                  ("Security code (CVV)", "Not collected or stored (PCI DSS)")]),
        Paragraph("3. Service and Charge Details", H2),
        kv_table([("Invoice number", s["invoice_no"]), ("Service purchased", s["service_name"]),
                  ("Description of service", s["description"]),
                  ("Amount to be charged (USD)", f"${s['amount']}"), ("Charge type", s["charge_type"]),
                  ("Date of charge", s["charge_date"]), ("Scheduled service date", s["service_date"])]),
        Paragraph("Important Disclosures (acknowledged by cardholder)", H2),
        *[Paragraph("• " + esc(d), SMALL) for d in DISCLOSURE],
        Spacer(1, 4),
        Paragraph("<b>Cancellation and refunds.</b> " + esc(REFUND_POLICY), SMALL),
        Paragraph("4. Authorization", H2), Paragraph(esc(AUTH_TEXT), BODY), Spacer(1, 8),
        *signature_block(r, sig_png),
        *esign_record(r),
        Spacer(1, 6),
        Paragraph("Card details are used only to process the payment above and are stored securely "
                  "or destroyed after processing.", SMALL),
    ]


def invoice_story(r, sig_png):
    c, s = r["customer"], r["service"]
    items = grid_table(
        [["Service", "Description", "Qty", "Amount (USD)"],
         [Paragraph(esc(s["service_name"]), BODY), Paragraph(esc(s["description"]), BODY),
          "1", f"${s['amount']}"],
         ["", "", Paragraph("<b>Total</b>", BODY), Paragraph(f"<b>${s['amount']}</b>", BODY)]],
        [1.6 * inch, 3.6 * inch, 0.6 * inch, 1.2 * inch])
    return [
        *header("Invoice / Service Agreement"),
        kv_table([("Invoice number", s["invoice_no"]), ("Invoice date", s["invoice_date"]),
                  ("Scheduled service date", s["service_date"])]),
        Paragraph("Bill To", H2), kv_table(bill_to_rows(c)),
        Paragraph("Services", H2), items,
        Paragraph("Payment", H2),
        kv_table([("Payment method", f"{c['card_type']} ending in {c['card_last4']}"),
                  ("Charge type", s["charge_type"]), ("Date of charge", s["charge_date"])]),
        Paragraph("Terms", H2),
        Paragraph("This fee covers planning and advisory services only and does not include the cost of any "
                  "flight, hotel, car rental or other third-party travel product. " + esc(REFUND_POLICY), SMALL),
        Paragraph("Customer Acceptance", H2), Paragraph(esc(INVOICE_ACCEPT_TEXT), BODY), Spacer(1, 8),
        *signature_block(r, sig_png),
        *esign_record(r),
    ]


def summary_story(r):
    """Cover page for the processing bank; mirrors their document checklist."""
    c, s, f = r["customer"], r["service"], r["fulfillment"]
    history = grid_table(
        [["Recorded", "Status", "Service date", "Notes"]] +
        [[h["recorded_at"], h["status"], h["date"] or "—", Paragraph(esc(h["notes"]), SMALL)]
         for h in f["history"]],
        [1.5 * inch, 1.1 * inch, 1.1 * inch, 3.3 * inch])
    date_label = "Date fulfilled" if f["status"] == "Fulfilled" else "Date service will be provided"
    return [
        *header("Transaction Summary &amp; Fulfillment Record"),
        Paragraph(f"Prepared {esc(now_utc())} for the processing bank. Attached: signed invoice and "
                  "signed Credit Card Authorization Form.", SMALL),
        Paragraph("Cardholder", H2),
        kv_table([("Full name", c["full_name"]), ("Phone number", c["phone"]),
                  ("Billing address", f"{c['address']}, {c['city_state_zip']}"), ("Email", c["email"])]),
        Paragraph("Transaction", H2),
        kv_table([("Invoice number", s["invoice_no"]), ("Amount (USD)", f"${s['amount']}"),
                  ("Card", f"{c['card_type']} ending in {c['card_last4']}"),
                  ("Date of charge", s["charge_date"]),
                  ("Signed by cardholder", r["audit"]["signed_at_utc"])]),
        Paragraph("Description of Service", H2),
        kv_table([("Service", s["service_name"]), ("Detailed description", s["description"])]),
        Paragraph("Fulfillment Status", H2),
        kv_table([("Current status", f["status"]), (date_label, f["date"] or "—")]),
        Paragraph("Fulfillment History", H2), history,
    ]


def evidence_packet(token, r):
    cover = io.BytesIO()
    build_pdf(cover, summary_story(r))
    cover.seek(0)
    writer = PdfWriter()
    writer.append(cover)
    writer.append(str(PDF_DIR / f"invoice_{token}.pdf"))
    writer.append(str(PDF_DIR / f"authorization_{token}.pdf"))
    out = io.BytesIO()
    writer.write(out)
    out.seek(0)
    return out


# ======================================================================
# HTML templates
# ======================================================================
CSS = """
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Signature Journeys – Secure Signing</title>
<style>
 body{font-family:system-ui,Arial,sans-serif;max-width:820px;margin:24px auto;padding:0 16px;color:#222}
 h1{font-size:22px} h2{font-size:17px;margin-top:26px;border-bottom:1px solid #ddd;padding-bottom:4px}
 label{display:block;margin-top:10px;font-weight:600;font-size:14px}
 input,select,textarea{width:100%;padding:8px;font-size:15px;box-sizing:border-box;margin-top:4px;font-family:inherit}
 .box{background:#f7f7f7;border:1px solid #ddd;padding:12px 16px;font-size:13px;border-radius:6px;white-space:pre-line}
 .box ul{white-space:normal}
 .err{background:#fdecea;color:#a00;padding:10px 14px;border-radius:6px}
 .hint{font-size:12px;color:#666;margin:4px 0 0}
 #sig{width:100%;height:180px;border:1px solid #999;border-radius:6px;touch-action:none;background:#fff}
 button{padding:10px 18px;font-size:15px;margin-top:14px;cursor:pointer}
 .row{display:flex;gap:12px}.row>div{flex:1}
 .check{display:flex;gap:8px;align-items:flex-start;font-weight:normal}.check input{width:auto;margin-top:3px}
 table.list{border-collapse:collapse;width:100%;font-size:14px}
 table.list td,table.list th{border:1px solid #ddd;padding:6px 8px;text-align:left;vertical-align:top}
</style>"""

ERRORS = """{% if errors %}<div class="err">{% for e in errors %}<div>{{e}}</div>{% endfor %}</div>{% endif %}"""

HOME_TPL = CSS + """
<h1>Signature Journeys – Secure Document Signing</h1>
<p>If you received a signing link from Signature Journeys, please open that link directly.</p>
<p>Questions? Call {{phone}} or email {{email}}.</p>"""

ADMIN_NEW_TPL = CSS + """
<p><a href="{{url_for('admin_list', key=key)}}">View all requests →</a></p>
<h1>Create signing request</h1>""" + ERRORS + """
{% if link %}<div class="box"><b>Send this link to the customer:</b>
<a href="{{link}}">{{link}}</a></div>{% endif %}
<form method="post">
 <label>Service</label>
 <select name="service" id="svc">{% for k,v in services.items() %}
  <option value="{{k}}" {% if f.service==k %}selected{% endif %}>{{v[0]}}{% if v[1] %} (${{v[1]}}){% endif %}</option>{% endfor %}
 </select>
 <div id="otherBox" style="display:none">
  <label>Service name</label>
  <input name="custom_name" id="customName" value="{{f.custom_name}}" placeholder="e.g. Honeymoon Planning Package – 3 sessions">
 </div>
 <label>Detailed description of service</label>
 <textarea name="description" rows="7" required placeholder="Example: Two 60-minute video planning sessions (Oct 12 and Oct 15) for a 10-day Italy trip (Rome, Florence, Venice), Dec 1–10, 2 travelers. Deliverables: written day-by-day itinerary with routes, timings and booking links; one round of revisions; email support until departure.">{{f.description}}</textarea>
 <p class="hint">Be specific: what the customer receives, number of sessions, deliverables, destinations, dates. This text appears on the invoice, the authorization form and the evidence packet.</p>
 <div class="row">
  <div><label>Amount (USD)</label><input name="amount" value="{{f.amount}}" placeholder="Blank = standard fee"></div>
  <div><label>Charge type</label><select name="charge_type">{% for t in ['One-time','Installment'] %}<option {% if f.charge_type==t %}selected{% endif %}>{{t}}</option>{% endfor %}</select></div>
 </div>
 <div class="row">
  <div><label>Date of charge</label><input type="date" name="charge_date" value="{{f.charge_date}}" required></div>
  <div><label>Scheduled service date</label><input type="date" name="service_date" value="{{f.service_date}}" required></div>
 </div>
 <label>Fulfillment status</label>
 <select name="status">{% for st in statuses %}<option {% if f.status==st %}selected{% endif %}>{{st}}</option>{% endfor %}</select>
 <button>Create link</button>
</form>
<script>
 const svc=document.getElementById('svc'),box=document.getElementById('otherBox'),cn=document.getElementById('customName');
 function toggle(){const o=svc.value==='other';box.style.display=o?'block':'none';cn.required=o;}
 svc.onchange=toggle;toggle();
</script>"""

ADMIN_LIST_TPL = CSS + """
<p><a href="{{url_for('admin_new', key=key)}}">+ New request</a></p>
<h1>All requests</h1>
<table class="list"><tr><th>Invoice</th><th>Customer</th><th>Service</th><th>Amount</th><th>Signed</th><th>Fulfillment</th><th></th></tr>
{% for r in records %}<tr>
 <td>{{r.service.invoice_no}}</td><td>{{r.customer.full_name if r.customer else '—'}}</td>
 <td>{{r.service.service_name}}</td><td>${{r.service.amount}}</td>
 <td>{{'Yes' if r.status=='signed' else 'Pending'}}</td><td>{{r.fulfillment.status}}</td>
 <td><a href="{{url_for('admin_record', token=r.token, key=key)}}">Open</a></td></tr>{% endfor %}
</table>"""

ADMIN_RECORD_TPL = CSS + """
<p><a href="{{url_for('admin_list', key=key)}}">← All requests</a></p>
<h1>{{r.service.invoice_no}} – {{r.service.service_name}}</h1>""" + ERRORS + """
<div class="box"><b>Amount:</b> ${{r.service.amount}} · <b>Charge date:</b> {{r.service.charge_date}} · <b>Scheduled:</b> {{r.service.service_date}}
<b>Description:</b>
{{r.service.description}}</div>
{% if r.status=='signed' %}
 <h2>Cardholder</h2>
 <div class="box">{{r.customer.full_name}} · {{r.customer.phone}} · {{r.customer.email}}
{{r.customer.address}}, {{r.customer.city_state_zip}}
Signed {{r.audit.signed_at_utc}} ({{'typed name' if r.audit.signature_method=='typed' else 'drawn signature'}})</div>
 <h2>Documents</h2>
 <p><a href="{{url_for('admin_evidence', token=r.token, key=key)}}"><b>Download evidence packet for processor</b></a>
  · <a href="{{url_for('customer_pdf', token=r.token, kind='invoice')}}">Signed invoice</a>
  · <a href="{{url_for('customer_pdf', token=r.token, kind='authorization')}}">Signed authorization form</a></p>
{% else %}
 <p><b>Not signed yet.</b> Customer link:
 <a href="{{url_for('sign', token=r.token, _external=True)}}">{{url_for('sign', token=r.token, _external=True)}}</a></p>
{% endif %}
<h2>Fulfillment</h2>
<form method="post">
 <div class="row">
  <div><label>Status</label><select name="status">{% for st in statuses %}<option {% if r.fulfillment.status==st %}selected{% endif %}>{{st}}</option>{% endfor %}</select></div>
  <div><label>Date fulfilled / will be provided</label><input type="date" name="date" value="{{r.fulfillment.date}}" required></div>
 </div>
 <label>Notes (what was delivered, how, and when)</label>
 <textarea name="notes" rows="3" placeholder="e.g. Itinerary PDF emailed to customer on Oct 16; video session held Oct 15, 45 min."></textarea>
 <button>Save update</button>
</form>
<h2>History</h2>
<table class="list"><tr><th>Recorded</th><th>Status</th><th>Date</th><th>Notes</th></tr>
{% for h in r.fulfillment.history %}<tr><td>{{h.recorded_at}}</td><td>{{h.status}}</td><td>{{h.date}}</td><td>{{h.notes}}</td></tr>{% endfor %}
</table>"""

SIGN_TPL = CSS + """
<link href="https://fonts.googleapis.com/css2?family=Dancing+Script:wght@600&display=swap" rel="stylesheet">
<style>
 .tabs{display:flex;gap:8px;margin:6px 0 10px}
 .tab{margin:0;padding:8px 14px;border:1px solid #999;background:#fff;border-radius:6px;font-size:14px}
 .tab.active{background:#222;color:#fff;border-color:#222}
 .typed-preview{font-family:'Dancing Script',cursive;font-size:42px;min-height:90px;border:1px solid #999;
   border-radius:6px;background:#fff;margin-top:8px;padding:10px 16px;display:flex;align-items:center}
</style>
<h1>Credit Card Authorization – Signature Journeys</h1>""" + ERRORS + """
<h2>Service and charge details</h2>
<div class="box"><b>Invoice:</b> {{s.invoice_no}}
<b>Service:</b> {{s.service_name}}
<b>Amount:</b> ${{s.amount}} USD · <b>Charge type:</b> {{s.charge_type}} · <b>Date of charge:</b> {{s.charge_date}}
<b>Scheduled service date:</b> {{s.service_date}}
<b>Description:</b>
{{s.description}}</div>
<h2>Important disclosures – please read</h2>
<div class="box"><ul>{% for d in disclosure %}<li>{{d}}</li>{% endfor %}</ul><b>Cancellation and refunds.</b> {{refund}}</div>
<form method="post" id="f">
 <h2>1. Cardholder information</h2>
 <label>Full name (as shown on card)</label><input name="full_name" value="{{f.full_name}}" required>
 <label>Billing address</label><input name="address" value="{{f.address}}" required>
 <label>City, state, ZIP</label><input name="city_state_zip" value="{{f.city_state_zip}}" required>
 <div class="row">
  <div><label>Phone</label><input name="phone" value="{{f.phone}}" required></div>
  <div><label>Email</label><input type="email" name="email" value="{{f.email}}" required></div>
 </div>
 <h2>2. Card information</h2>
 <label>Card type</label>
 <select name="card_type">{% for t in ['Visa','Mastercard','Amex','Discover'] %}<option {% if f.card_type==t %}selected{% endif %}>{{t}}</option>{% endfor %}</select>
 <div class="row">
  <div><label>Card number</label><input name="card_number" inputmode="numeric" autocomplete="cc-number" required></div>
  <div><label>Expiry (MM/YY)</label><input name="expiry" value="{{f.expiry}}" placeholder="MM/YY" autocomplete="cc-exp" required></div>
 </div>
 <p class="hint">Only the last 4 digits are kept on the signed documents. Your full card number and security code are not stored.</p>
 <h2>4. Authorization</h2>
 <div class="box">{{auth}}</div>
 <label class="check"><input type="checkbox" name="agree" value="yes">
  I have read the disclosures above, agree to sign electronically (drawn or typed signature), accept the invoice for these services, and authorize this charge.</label>
 <label>Printed name</label><input name="printed_name" id="printedName" value="{{f.printed_name}}" required>

 <label>Signature</label>
 <div class="tabs">
  <button type="button" class="tab active" data-mode="drawn">Draw signature</button>
  <button type="button" class="tab" data-mode="typed">Type name instead</button>
 </div>
 <div id="drawPane">
  <canvas id="sig"></canvas>
  <button type="button" id="clear">Clear signature</button>
 </div>
 <div id="typePane" style="display:none">
  <input id="typedName" name="typed_name" value="{{f.typed_name}}" placeholder="Type your full name" autocomplete="off">
  <div id="typedPreview" class="typed-preview"></div>
  <p class="hint">By typing your name, you adopt it as your legal electronic signature. It must match your printed name.</p>
 </div>
 <input type="hidden" name="signature" id="signature">
 <input type="hidden" name="sig_method" id="sigMethod" value="drawn">
 <br><button type="submit">Sign and submit</button>
</form>
<script>
// ---- Drawn signature pad
const c=document.getElementById('sig'),ctx=c.getContext('2d');let drawing=false,hasInk=false,mode='drawn';
function setup(){const r=window.devicePixelRatio||1;c.width=c.offsetWidth*r;c.height=c.offsetHeight*r;
 ctx.setTransform(r,0,0,r,0,0);ctx.fillStyle='#fff';ctx.fillRect(0,0,c.width,c.height);
 ctx.lineWidth=2.2;ctx.lineCap='round';ctx.lineJoin='round';ctx.strokeStyle='#000';hasInk=false;}
setup();
function pos(e){const b=c.getBoundingClientRect();return[e.clientX-b.left,e.clientY-b.top];}
c.addEventListener('pointerdown',e=>{drawing=true;hasInk=true;c.setPointerCapture(e.pointerId);const[x,y]=pos(e);ctx.beginPath();ctx.moveTo(x,y);});
c.addEventListener('pointermove',e=>{if(!drawing)return;const[x,y]=pos(e);ctx.lineTo(x,y);ctx.stroke();});
['pointerup','pointercancel'].forEach(ev=>c.addEventListener(ev,()=>drawing=false));
document.getElementById('clear').onclick=setup;

// ---- Draw / Type tabs
const tabs=document.querySelectorAll('.tab'),tn=document.getElementById('typedName'),pv=document.getElementById('typedPreview');
function setMode(m){mode=m;document.getElementById('sigMethod').value=m;
 tabs.forEach(t=>t.classList.toggle('active',t.dataset.mode===m));
 document.getElementById('drawPane').style.display=m==='drawn'?'block':'none';
 document.getElementById('typePane').style.display=m==='typed'?'block':'none';
 if(m==='drawn')setup();}
tabs.forEach(t=>t.onclick=()=>setMode(t.dataset.mode));
tn.oninput=()=>pv.textContent=tn.value;pv.textContent=tn.value;
if('{{f.sig_method}}'==='typed')setMode('typed');

// ---- Render typed name as a signature image
async function typedToPng(text){
 try{await document.fonts.load('60px "Dancing Script"');}catch(e){}
 const cv=document.createElement('canvas');cv.width=900;cv.height=220;const x=cv.getContext('2d');
 x.fillStyle='#fff';x.fillRect(0,0,cv.width,cv.height);
 let size=80;const setFont=()=>x.font=`600 ${size}px "Dancing Script", cursive`;setFont();
 while(x.measureText(text).width>860&&size>28){size-=4;setFont();}
 x.fillStyle='#000';x.textBaseline='middle';x.fillText(text,20,110);
 return cv.toDataURL('image/png');}

// ---- Submit
const norm=s=>s.trim().replace(/\\s+/g,' ').toLowerCase();
const form=document.getElementById('f'),sigInput=document.getElementById('signature');
form.addEventListener('submit',async e=>{
 e.preventDefault();
 if(mode==='drawn'){
  if(!hasInk){alert('Please draw your signature, or choose "Type name instead".');return;}
  sigInput.value=c.toDataURL('image/png');
 }else{
  const t=tn.value.trim();
  if(!t){alert('Please type your name as your signature.');return;}
  if(norm(t)!==norm(document.getElementById('printedName').value)){alert('Your typed signature must match your printed name exactly.');return;}
  sigInput.value=await typedToPng(t);
 }
 form.submit();
});
</script>"""

DONE_TPL = CSS + """
<h1>Thank you – your documents are signed</h1>
<p>Please download and keep copies for your records:</p>
<p><a href="{{url_for('customer_pdf', token=token, kind='authorization')}}">Signed Credit Card Authorization Form</a><br>
<a href="{{url_for('customer_pdf', token=token, kind='invoice')}}">Signed Invoice</a></p>"""


# ======================================================================
# Public routes
# ======================================================================
@app.route("/")
def home():
    return render_template_string(HOME_TPL, phone=COMPANY["phone"], email=COMPANY["email"])


@app.after_request
def security_headers(resp):
    resp.headers["X-Content-Type-Options"] = "nosniff"
    resp.headers["X-Frame-Options"] = "DENY"
    resp.headers["Referrer-Policy"] = "no-referrer"
    resp.headers["Cache-Control"] = "no-store"
    return resp


# ======================================================================
# Admin routes
# ======================================================================
@app.route("/admin", methods=["GET", "POST"])
def admin_new():
    require_admin()
    key, link, errors, form = request.args["key"], None, [], {}
    if request.method == "POST":
        form = request.form
        errors, parsed = validate_request(form)
        if not errors:
            name, amount = parsed
            token = secrets.token_urlsafe(24)
            save(token, {
                "token": token, "status": "pending", "created_at_utc": now_utc(),
                "service": {
                    "invoice_no": f"SJ-{datetime.now():%Y%m%d}-{secrets.randbelow(90000) + 10000}",
                    "invoice_date": datetime.now().strftime("%Y-%m-%d"),
                    "service_name": name,
                    "description": form["description"].strip(),
                    "amount": amount,
                    "charge_type": form.get("charge_type", "One-time"),
                    "charge_date": form["charge_date"],
                    "service_date": form["service_date"],
                },
                "fulfillment": {
                    "status": form["status"], "date": form["service_date"],
                    "history": [{"recorded_at": now_utc(), "status": form["status"],
                                 "date": form["service_date"], "notes": "Request created"}],
                },
            })
            link, form = url_for("sign", token=token, _external=True), {}
    return render_template_string(ADMIN_NEW_TPL, services=SERVICES, statuses=STATUSES,
                                  link=link, errors=errors, f=form, key=key)


@app.route("/admin/list")
def admin_list():
    require_admin()
    records = [json.loads(p.read_text()) for p in DATA_DIR.glob("*.json")]
    records.sort(key=lambda r: r["created_at_utc"], reverse=True)
    return render_template_string(ADMIN_LIST_TPL, records=records, key=request.args["key"])


@app.route("/admin/record/<token>", methods=["GET", "POST"])
def admin_record(token):
    require_admin()
    r, errors = load(token), []
    if request.method == "POST":
        status, date = request.form.get("status"), request.form.get("date", "")
        if status not in STATUSES or not date:
            errors.append("Choose a status and a date.")
        else:
            r["fulfillment"].update(status=status, date=date)
            r["fulfillment"]["history"].append({
                "recorded_at": now_utc(), "status": status, "date": date,
                "notes": request.form.get("notes", "").strip()})
            save(token, r)
            return redirect(url_for("admin_record", token=token, key=request.args["key"]))
    return render_template_string(ADMIN_RECORD_TPL, r=r, statuses=STATUSES,
                                  errors=errors, key=request.args["key"])


@app.route("/admin/evidence/<token>")
def admin_evidence(token):
    require_admin()
    r = load(token)
    if r["status"] != "signed":
        abort(404)
    return send_file(evidence_packet(token, r), as_attachment=True, mimetype="application/pdf",
                     download_name=f"Evidence_{r['service']['invoice_no']}.pdf")


# ======================================================================
# Customer routes
# ======================================================================
@app.route("/sign/<token>", methods=["GET", "POST"])
def sign(token):
    r = load(token)
    if r["status"] == "signed":
        return render_template_string(DONE_TPL, token=token)

    ctx = dict(s=r["service"], disclosure=DISCLOSURE, refund=REFUND_POLICY, auth=AUTH_TEXT)
    if request.method == "GET":
        return render_template_string(SIGN_TPL, f={}, errors=[], **ctx)

    f = request.form
    errors, card_num = validate_customer(f)
    sig_png = None
    if not errors:
        try:
            sig_png = base64.b64decode(f["signature"].split(",", 1)[1], validate=True)
        except Exception:
            errors.append("Signature could not be read. Please sign again.")
    if errors:
        return render_template_string(SIGN_TPL, f=f, errors=errors, **ctx), 400

    r["customer"] = {
        "full_name": f["full_name"].strip(), "address": f["address"].strip(),
        "city_state_zip": f["city_state_zip"].strip(), "phone": f["phone"].strip(),
        "email": f["email"].strip(), "card_type": f["card_type"], "card_last4": card_num[-4:],
        "expiry": f["expiry"].strip(), "printed_name": f["printed_name"].strip(),
    }
    method = f.get("sig_method", "drawn")
    r["audit"] = {
        "signed_at_utc": now_utc(),
        "consent_checkbox": True,
        "signature_method": method,
        "typed_name": " ".join(f.get("typed_name", "").split()) if method == "typed" else "",
        "user_agent": request.headers.get("User-Agent", ""),
    }
    del card_num  # full card number is never written anywhere

    (DATA_DIR / f"{token}_sig.png").write_bytes(sig_png)
    hashes = {}
    for kind, story_fn in (("authorization", authorization_story), ("invoice", invoice_story)):
        path = PDF_DIR / f"{kind}_{token}.pdf"
        build_pdf(str(path), story_fn(r, sig_png))
        hashes[kind] = hashlib.sha256(path.read_bytes()).hexdigest()
    r["pdf_sha256"], r["status"] = hashes, "signed"
    save(token, r)
    return render_template_string(DONE_TPL, token=token)


@app.route("/pdf/<token>/<kind>")
def customer_pdf(token, kind):
    if kind not in ("authorization", "invoice"):
        abort(404)
    r = load(token)
    if r["status"] != "signed":
        abort(404)
    return send_file(PDF_DIR / f"{kind}_{token}.pdf", as_attachment=True,
                     download_name=f"{kind.capitalize()}_{r['service']['invoice_no']}.pdf")


if __name__ == "__main__":
    app.run(debug=os.environ.get("FLASK_DEBUG") == "1")
