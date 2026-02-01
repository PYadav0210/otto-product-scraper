"""
Otto.de Product Information Scraper

Scrapes product data from otto.de including:
- Product URLs
- PDF product datasheet links

Mimics human browsing behavior with delays and realistic interactions.
"""

from pathlib import Path
from dataclasses import dataclass, asdict
from typing import Optional, Tuple
import csv
import time
import random
import logging
import io
import re
import urllib.request
import urllib.error

from playwright.sync_api import sync_playwright, Page


# ============================================================================
# CONFIGURATION
# ============================================================================

class Config:
    """Application configuration"""
    INPUT_FILE = "article_numbers.txt"
    OUTPUT_FILE = "otto_products_report.csv"
    
    # Browser settings
    HEADLESS = False
    SLOW_MO = 20
    VIEWPORT_WIDTH = 1920
    VIEWPORT_HEIGHT = 1080
    
    # Human-like delays (seconds)
    MIN_DELAY = 0.15
    MAX_DELAY = 0.5
    KEYSTROKE_DELAY_MIN = 0.01
    KEYSTROKE_DELAY_MAX = 0.03
    ACTION_DELAY_MIN = 0.02
    ACTION_DELAY_MAX = 0.08
    SCROLL_MIN = 200
    SCROLL_MAX = 700
    DEFAULT_TIMEOUT_MS = 15000

    # OCR settings (for image-only PDFs)
    OCR_ENABLED = True
    OCR_DPI = 200
    OCR_LANG = "eng+deu"
    POPPLER_PATH = "/opt/homebrew/bin"
    TESSERACT_CMD = "/opt/homebrew/bin/tesseract"


# ============================================================================
# DATA MODELS
# ============================================================================

@dataclass
class ProductData:
    """Product information"""
    input_ean: str
    product_url: str
    pdf_link: str
    energy_efficiency_class: str
    supplier_information: str


# ============================================================================
# LOGGING
# ============================================================================

def setup_logging() -> logging.Logger:
    """Configure logging"""
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(message)s'
    )
    return logging.getLogger(__name__)


logger = setup_logging()


# ============================================================================
# BROWSER INTERACTION
# ============================================================================

class BrowserHelper:
    """Helper methods for browser interaction"""
    
    @staticmethod
    def human_type(element, text: str) -> None:
        """Type text with human-like pauses"""
        element.click()
        element.fill("")
        
        for char in text:
            element.type(char)
            time.sleep(random.uniform(
                Config.KEYSTROKE_DELAY_MIN,
                Config.KEYSTROKE_DELAY_MAX
            ))
    
    @staticmethod
    def random_mouse_move(page: Page) -> None:
        """Move mouse to random position"""
        try:
            page.mouse.move(
                random.randint(100, 500),
                random.randint(100, 500)
            )
        except:
            pass
    
    @staticmethod
    def random_scroll(page: Page) -> None:
        """Small random scroll to mimic browsing"""
        try:
            page.mouse.wheel(
                0,
                random.randint(Config.SCROLL_MIN, Config.SCROLL_MAX)
            )
        except:
            pass
    
    @staticmethod
    def human_delay() -> float:
        """Get random delay between requests"""
        return random.uniform(Config.MIN_DELAY, Config.MAX_DELAY)
    
    @staticmethod
    def action_delay() -> float:
        """Short delay between interactions"""
        return random.uniform(Config.ACTION_DELAY_MIN, Config.ACTION_DELAY_MAX)


class OttoNavigator:
    """Navigate otto.de and extract product information"""
    
    def __init__(self, page: Page):
        self.page = page
        self._cookies_accepted = False
    
    def accept_cookies(self) -> None:
        """Click cookie consent if present"""
        try:
            if self._cookies_accepted:
                return
            time.sleep(random.uniform(0.6, 1.2))
            button = self.page.locator("#onetrust-accept-btn-handler")
            if button.count() > 0:
                button.click(timeout=5000)
                logger.info("Cookies accepted")
                time.sleep(random.uniform(0.3, 0.7))
            self._cookies_accepted = True
        except:
            pass
    
    def search_product(self, query: str) -> None:
        """Navigate to otto.de and search for product"""
        logger.info(f"Navigating to Otto.de and searching for: {query}")
        self.page.goto("https://www.otto.de/", wait_until="domcontentloaded")
        
        self.accept_cookies()
        BrowserHelper.random_mouse_move(self.page)
        time.sleep(BrowserHelper.action_delay())
        
        # Find search input
        search_box = None
        selectors = [
            "input[type='search']",
            "input[name='q']",
            "input[placeholder*='Suchen' i]",
            "header input"
        ]
        
        for selector in selectors:
            try:
                element = self.page.locator(selector).first
                element.wait_for(state="visible", timeout=10000)
                search_box = element
                break
            except:
                continue
        
        if not search_box:
            raise Exception("Search box not found")
        
        # Type and search
        BrowserHelper.human_type(search_box, query)
        time.sleep(BrowserHelper.action_delay())
        search_box.press("Enter")
        
        logger.info("Waiting for search results...")
        self.page.wait_for_load_state("domcontentloaded")
        try:
            self.page.wait_for_selector("article", timeout=6000)
        except:
            pass
    
    def find_product(self, query: str) -> bool:
        """Find main product (skip sponsored items and accessories)"""
        # Already on product page?
        if "/p/" in self.page.url:
            logger.info(f"Already on product page: {self.page.url}")
            return True
        
        logger.info("Looking for actual product in search results...")
        try:
            self.page.wait_for_selector("article", timeout=8000)
        except:
            pass
        query_norm = self._normalize_text(query)
        model_number = self._extract_model_number(query_norm)
        required_tokens = self._tokenize_query_loose(query_norm)

        def collect_candidates(enforce_model: bool) -> list[tuple[int, int, object, str, str, int, bool]]:
            articles = self.page.locator("article").all()
            candidates: list[tuple[int, int, object, str, str, int, bool]] = []
            for idx, article in enumerate(articles):
                try:
                    text = article.inner_text().lower()
                    title_text = self._extract_title_text(article)
                    raw_title = title_text.lower() if title_text else ""
                    title_norm = self._normalize_text(title_text) if title_text else ""
                    card_norm = self._normalize_text(text)
                    
                    # Skip sponsored items
                    if "gesponsert" in text or "anzeige" in text:
                        continue

                    # Skip accessories unless the query explicitly asks for them
                    if not self._query_allows_accessories(query_norm):
                        accessories = {
                            'hülle', 'huelle', 'case', 'cover', 'kabel', 'ladegerät', 'ladegeraet',
                            'adapter', 'kopfhörer', 'kopfhoerer', 'displayschutz', 'folie',
                            'schutzfolie', 'schutzglas', 'panzerglas', 'panzerfolie',
                            'charger', 'earphone', 'earphones', 'tasche', 'pouch', 'bumper',
                            'handyhülle', 'handyhuelle', 'schale', 'displayfolie', 'screen', 'protector',
                            'schutzhülle', 'schutzhuelle',
                            'akku', 'ersatzakku', 'battery', 'replacement', 'handyakku'
                        }
                        is_accessory = (
                            any(acc in title_norm for acc in accessories)
                            or any(acc in card_norm for acc in accessories)
                            or any(acc in raw_title for acc in accessories)
                            or any(acc in text for acc in accessories)
                        )
                        if is_accessory:
                            continue
                    
                    # Enforce same model number (use full card text for reliability)
                    model_match = False
                    if model_number:
                        model_match = self._matches_model_number_near_brand(card_norm, model_number)
                    if enforce_model and model_number and not model_match:
                        continue
                    if enforce_model and model_number and self._has_conflicting_model_number(card_norm, model_number):
                        continue
                    
                    # Require a minimal token overlap to avoid false positives
                    if required_tokens and self._match_score_tokens(card_norm, required_tokens) < max(1, len(required_tokens) // 3):
                        continue

                    # Score by token overlap (title preferred, then card)
                    score = self._match_score_tokens(title_norm or card_norm, required_tokens)
                    if model_match:
                        score += 5
                    
                    link = article.locator("a[href*='/p/']").first
                    if link.count() > 0:
                        candidates.append((score, idx, link, title_norm or card_norm, card_norm, score, model_match))
                except Exception:
                    continue
            return candidates

        # Try several scroll passes to find the same model before giving up
        for attempt in range(6):
            candidates = collect_candidates(enforce_model=False)
            if candidates:
                model_candidates = [c for c in candidates if c[6]]
                if model_candidates:
                    candidates = model_candidates
                candidates.sort(key=lambda x: (-x[0], x[1]))
                _, idx, link, _, _, _, _ = candidates[0]
                logger.info(f"Found product at position #{idx}")
                BrowserHelper.random_mouse_move(self.page)
                time.sleep(BrowserHelper.action_delay())
                link.click()
                try:
                    self.page.wait_for_url("**/p/**", timeout=8000)
                except:
                    pass
                self.page.wait_for_load_state("domcontentloaded")
                time.sleep(BrowserHelper.action_delay())
                logger.info(f"Product URL: {self.page.url}")
                return True
            # Scroll to load more results and retry
            try:
                self.page.mouse.wheel(0, 1200)
                time.sleep(BrowserHelper.action_delay())
            except:
                pass

        logger.error("No suitable product found")
        return False

    def _normalize_text(self, text: str) -> str:
        """Normalize text for token matching."""
        text = text.lower()
        text = re.sub(r"[^a-z0-9]+", " ", text)
        return re.sub(r"\s+", " ", text).strip()

    def _extract_model_number(self, query_norm: str) -> str:
        """Extract model number like 16/17 from query."""
        # Prefer numbers attached to a known brand (e.g., iphone16)
        compact = re.sub(r"\s+", "", query_norm)
        match = re.search(r"(iphone|ipad|galaxy|pixel)(\d{2})", compact)
        if match:
            return match.group(2)
        # Fallback: standalone two-digit number
        match = re.search(r"\b(\d{2})\b", query_norm)
        if match:
            return match.group(1)
        return ""

    def _variant_preference(self, query_norm: str) -> list[str]:
        """Return preferred variants in order based on query."""
        has_pro = "pro" in query_norm
        has_max = "max" in query_norm
        if has_pro and has_max:
            return ["pro max", "pro", "max", "base"]
        if has_pro:
            return ["pro", "base"]
        if has_max:
            return ["max", "base"]
        return ["base"]

    def _matches_variant(self, title_norm: str, variant: str) -> bool:
        """Check if title matches variant."""
        if variant == "pro max":
            return "pro" in title_norm and "max" in title_norm
        if variant == "pro":
            return "pro" in title_norm and "max" not in title_norm
        if variant == "max":
            return "max" in title_norm and "pro" not in title_norm
        return ("pro" not in title_norm) and ("max" not in title_norm)

    def _tokenize_query_loose(self, query_norm: str) -> list[str]:
        """Tokenize query for loose matching (ignore storage/color/noise)."""
        noise = {"gb", "tb", "speicher", "farbe", "schwarz", "weiß", "weiss", "silber", "rot", "blau", "gruen", "grün"}
        return [t for t in query_norm.split() if t and t not in noise]

    def _match_score_tokens(self, text_norm: str, query_tokens: list[str]) -> int:
        """Score by overlap of query tokens with text."""
        score = 0
        for t in query_tokens:
            if re.search(rf"\b{re.escape(t)}\b", text_norm):
                score += 1
        return score

    def _query_allows_accessories(self, query_norm: str) -> bool:
        """Return True if the query is explicitly for accessories."""
        accessory_tokens = {
            "hülle", "huelle", "case", "cover", "kabel", "ladegerät", "ladegeraet",
            "adapter", "kopfhörer", "kopfhoerer", "earphone", "earphones", "charger",
            "displayschutz", "folie", "schutzfolie", "tasche"
        }
        return any(tok in query_norm for tok in accessory_tokens)


    def _has_conflicting_model_number(self, text_norm: str, model_number: str) -> bool:
        """Return True if another two-digit model number appears near iPhone."""
        tokens = text_norm.split()
        if "iphone" not in tokens:
            return False
        for i, tok in enumerate(tokens):
            if tok != "iphone":
                continue
            window = tokens[i + 1 : i + 6]
            found_models = [t for t in window if re.fullmatch(r"\d{2}", t)]
            if found_models and any(m != model_number for m in found_models):
                return True
        return False

    def _matches_model_number_near_brand(self, text_norm: str, model_number: str) -> bool:
        """Match model number only when it appears next to the brand token (e.g., 'iphone 16')."""
        tokens = text_norm.split()
        if "iphone" not in tokens:
            return False
        for i, tok in enumerate(tokens):
            if tok != "iphone":
                continue
            # Look ahead a few tokens for the model number
            window = tokens[i + 1 : i + 5]
            found_models = [t for t in window if re.fullmatch(r"\d{2}", t)]
            if found_models:
                return model_number in found_models
        # Fallback: compact match like iphone16
        compact = text_norm.replace(" ", "")
        return re.search(rf"(iphone){re.escape(model_number)}", compact) is not None

    def _has_model_number(self, text_norm: str, model_number: str) -> bool:
        """Check if a specific model number appears anywhere."""
        return re.search(rf"\b{re.escape(model_number)}\b", text_norm) is not None

    def _title_has_other_models(self, title_norm: str, model_number: str) -> bool:
        """Reject titles that contain a different two-digit model number."""
        models = re.findall(r"\b(\d{2})\b", title_norm)
        return any(m != model_number for m in models)

    def _title_looks_like_phone(self, title_norm: str) -> bool:
        """Filter out accessories by requiring phone-like keywords."""
        return any(word in title_norm for word in ["smartphone", "handy", "mobiltelefon"])

    def _extract_title_text(self, article) -> str:
        """Extract product title text from search result article."""
        try:
            link = article.locator("a[href*='/p/']").first
            if link.count() > 0:
                aria = link.get_attribute("aria-label")
                if aria:
                    return aria
                text = link.inner_text()
                if text:
                    return text
        except:
            pass
        try:
            heading = article.locator("h2, h3").first
            if heading.count() > 0:
                return heading.inner_text()
        except:
            pass
        return ""
    
    def get_pdf_link(self) -> str:
        """Extract PDF link from Produktdatenblatt section"""
        try:
            logger.info("Looking for product datasheet (Produktdatenblatt)...")
            time.sleep(BrowserHelper.action_delay())
            
            # Prefer href extraction to avoid opening new tabs
            link = self.page.locator("a:has-text('Produktdatenblatt')").first
            if link.count() > 0:
                href = link.get_attribute("href")
                if href and ".pdf" in href.lower():
                    logger.info(f"Found PDF (direct link): {href}")
                    return href
            
            # Find and click datasheet link (fallback)
            elements = self.page.get_by_text("Produktdatenblatt").all()
            
            for element in elements:
                try:
                    # If the element is already a link to PDF, grab it without clicking
                    href = element.get_attribute("href")
                    if href and ".pdf" in href.lower():
                        logger.info(f"Found PDF (direct link): {href}")
                        return href
                    
                    element.scroll_into_view_if_needed()
                    BrowserHelper.random_scroll(self.page)
                    time.sleep(BrowserHelper.action_delay())
                    element.click(timeout=3000)
                    logger.info("Clicked datasheet link")
                    time.sleep(random.uniform(0.8, 1.6))
                    
                    # Look for PDF link in page
                    pdf_links = self.page.locator("a[href*='d.otto.de'][href*='.pdf']").all()
                    
                    if pdf_links:
                        href = pdf_links[0].get_attribute("href")
                        if href:
                            logger.info(f"Found PDF: {href}")
                            return href
                    
                except Exception as e:
                    logger.debug(f"Error processing element: {e}")
            
            logger.warning("PDF not found")
            return "Not found"
            
        except Exception as e:
            logger.error(f"Error extracting PDF link: {e}")
            return "Not found"


# ============================================================================
# MAIN SCRAPER
# ============================================================================

class Scraper:
    """Main scraper orchestrator"""
    
    def __init__(self):
        self.config = Config()
    
    def load_queries(self) -> list[str]:
        """Load search queries from input file"""
        path = Path(self.config.INPUT_FILE)
        
        if not path.exists():
            raise FileNotFoundError(f"Input file not found: {self.config.INPUT_FILE}")
        
        queries = [line.strip() for line in path.read_text(encoding="utf-8").split('\n') if line.strip()]
        
        if not queries:
            raise ValueError("Input file is empty")
        
        logger.info(f"Loaded {len(queries)} queries")
        return queries
    
    def scrape_product(self, navigator: OttoNavigator, query: str) -> Optional[ProductData]:
        """Scrape product data"""
        try:
            # Search and navigate
            navigator.search_product(query)
            
            if not navigator.find_product(query):
                return None
            
            product_url = navigator.page.url
            pdf_link = navigator.get_pdf_link()
            energy_class, supplier_info = self.extract_pdf_fields(pdf_link)
            
            # Create result
            result = ProductData(
                input_ean=query,
                product_url=product_url,
                pdf_link=pdf_link,
                energy_efficiency_class=energy_class,
                supplier_information=supplier_info
            )
            
            logger.info(f"✓ Scraped: {query}")
            return result
            
        except Exception as e:
            logger.error(f"Error scraping {query}: {e}")
            return None
    
    def run(self) -> None:
        """Execute scraping workflow"""
        queries = self.load_queries()
        
        with sync_playwright() as p:
            browser = p.chromium.launch(
                headless=self.config.HEADLESS,
                slow_mo=self.config.SLOW_MO
            )
            
            context = browser.new_context(
                viewport={
                    "width": self.config.VIEWPORT_WIDTH,
                    "height": self.config.VIEWPORT_HEIGHT
                },
                user_agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
                accept_downloads=False
            )
            page = context.new_page()
            page.route("**/*.pdf", lambda route: route.abort())
            page.on("popup", lambda popup: popup.close())
            page.set_default_timeout(self.config.DEFAULT_TIMEOUT_MS)
            page.set_default_navigation_timeout(self.config.DEFAULT_TIMEOUT_MS)
            navigator = OttoNavigator(page)
            
            # Write CSV
            fieldnames = [
                "input_ean",
                "product_url",
                "pdf_link",
                "energy_efficiency_class",
                "supplier_information"
            ]
            
            with open(self.config.OUTPUT_FILE, "w", newline="", encoding="utf-8") as f:
                writer = csv.DictWriter(f, fieldnames=fieldnames)
                writer.writeheader()
                
                for i, query in enumerate(queries, 1):
                    logger.info(f"\n{'='*60}")
                    logger.info(f"Processing [{i}/{len(queries)}]: {query}")
                    logger.info(f"{'='*60}")
                    
                    product = self.scrape_product(navigator, query)
                    
                    if product:
                        writer.writerow(asdict(product))
                        f.flush()
                    else:
                        # Record the query even when no product is found
                        writer.writerow({
                            "input_ean": query,
                            "product_url": "",
                            "pdf_link": "",
                            "energy_efficiency_class": "",
                            "supplier_information": ""
                        })
                        f.flush()
                    
                    # Delay before next product
                    if i < len(queries):
                        delay = BrowserHelper.human_delay()
                        logger.info(f"Waiting {delay:.1f}s before next search...")
                        time.sleep(delay)
            
            browser.close()
        
        logger.info(f"\n{'='*60}")
        logger.info(f"✓ Complete! Results: {self.config.OUTPUT_FILE}")
        logger.info(f"{'='*60}")

    def extract_pdf_fields(self, pdf_url: str) -> Tuple[str, str]:
        """Download PDF and extract energy class + supplier info."""
        if not pdf_url or pdf_url == "Not found":
            return ("Not found", "Not found")
        
        pdf_bytes = self.fetch_pdf_bytes(pdf_url)
        if not pdf_bytes:
            return ("Not found", "Not found")
        
        return self.parse_pdf_fields(pdf_bytes)
    
    def fetch_pdf_bytes(self, url: str) -> Optional[bytes]:
        """Fetch PDF bytes with stdlib (no browser download)."""
        try:
            req = urllib.request.Request(
                url,
                headers={
                    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
                    "Accept": "application/pdf"
                }
            )
            with urllib.request.urlopen(req, timeout=20) as resp:
                return resp.read()
        except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError) as e:
            logger.warning(f"PDF download failed: {e}")
            return None
    
    def parse_pdf_fields(self, pdf_bytes: bytes) -> Tuple[str, str]:
        """Extract fields from PDF text, preferring page 6/25 if present."""
        pages = self._extract_pdf_pages_text(pdf_bytes)
        if not pages:
            pages = []
        
        # Prefer specified pages if they exist; otherwise search all pages
        energy_pages = []
        supplier_pages = []
        if len(pages) >= 6:
            energy_pages = [pages[5]]
        if len(pages) >= 25:
            supplier_pages = [pages[24]]
        
        if not energy_pages:
            energy_pages = pages
        if not supplier_pages:
            supplier_pages = pages
        
        energy = self._extract_energy_class_from_pages(energy_pages)
        supplier = self._extract_supplier_info_from_pages(supplier_pages)
        
        # If not found and OCR enabled, try OCR fallback
        if self.config.OCR_ENABLED and (not energy or not supplier):
            ocr_pages = self._extract_pdf_pages_text_ocr(pdf_bytes)
            if ocr_pages:
                if not energy:
                    energy = self._extract_energy_class_from_pages(ocr_pages)
                if not supplier:
                    supplier = self._extract_supplier_info_from_pages(ocr_pages)

        return (energy or "Not found", supplier or "Not found")
    
    def _extract_pdf_pages_text(self, pdf_bytes: bytes) -> list[str]:
        """Extract text for all pages using available PDF parser."""
        try:
            import pdfplumber  # type: ignore
            with pdfplumber.open(io.BytesIO(pdf_bytes)) as pdf:
                return [page.extract_text() or "" for page in pdf.pages]
        except Exception:
            try:
                from PyPDF2 import PdfReader  # type: ignore
                reader = PdfReader(io.BytesIO(pdf_bytes))
                return [(page.extract_text() or "") for page in reader.pages]
            except Exception as e:
                logger.warning(f"PDF parsing failed: {e}")
                return []

    def _extract_pdf_pages_text_ocr(self, pdf_bytes: bytes) -> list[str]:
        """OCR text from PDF pages using tesseract."""
        try:
            from pdf2image import convert_from_bytes, pdfinfo_from_bytes  # type: ignore
            import pytesseract  # type: ignore
        except Exception as e:
            logger.warning(f"OCR dependencies missing: {e}")
            return []

        try:
            info = pdfinfo_from_bytes(pdf_bytes, poppler_path=self.config.POPPLER_PATH)
            page_count = int(info.get("Pages", 0))
        except Exception:
            page_count = 0

        page_numbers = []
        if page_count >= 25:
            page_numbers = [6, 25]
        elif page_count >= 6:
            page_numbers = [6]
        elif page_count > 0:
            page_numbers = list(range(1, page_count + 1))
        else:
            page_numbers = [1]

        ocr_texts = []
        for page_number in page_numbers:
            try:
                images = convert_from_bytes(
                    pdf_bytes,
                    dpi=self.config.OCR_DPI,
                    fmt="png",
                    first_page=page_number,
                    last_page=page_number,
                    poppler_path=self.config.POPPLER_PATH
                )
                if images:
                    pytesseract.pytesseract.tesseract_cmd = self.config.TESSERACT_CMD
                    try:
                        text = pytesseract.image_to_string(images[0], lang=self.config.OCR_LANG) or ""
                    except Exception:
                        text = pytesseract.image_to_string(images[0], lang="eng") or ""
                    ocr_texts.append(text)
            except Exception as e:
                logger.warning(f"OCR failed for page {page_number}: {e}")

        return ocr_texts
    
    def _extract_labeled_value_across_pages(
        self,
        pages: list[str],
        labels: list[str],
        value_pattern: Optional[str] = None
    ) -> str:
        """Find a label in any page and return value from same/next line."""
        for text in pages:
            value = self._extract_labeled_value(text, labels, value_pattern)
            if value:
                return value
        return ""

    def _extract_energy_class_from_pages(self, pages: list[str]) -> str:
        """Extract energy class (A-G/+++) from any page text."""
        for text in pages:
            if not text:
                continue
            # Try direct regex on full text
            match = re.search(
                r"(Energy\\s*efficiency\\s*class|Energieeffizienzklasse)\\s*[:\\-]?\\s*([A-G][+]{0,3})",
                text,
                re.I
            )
            if match:
                return match.group(2)
            # Fallback to line-based label
            value = self._extract_labeled_value(
                text,
                ["Energy efficiency class", "Energieeffizienzklasse"],
                value_pattern=r"[A-G][+]{0,3}"
            )
            if value:
                return value
        return ""

    def _extract_supplier_info_from_pages(self, pages: list[str]) -> str:
        """Extract supplier info block from any page text."""
        labels_after = [
            "Supplier information",
            "Lieferanteninformation",
            "Anschrift des Lieferanten"
        ]
        labels_before = [
            "Supplier's address",
            "Supplier address",
            "Lieferant",
            "Supplier"
        ]
        for text in pages:
            if not text:
                continue
            # German label sometimes appears inline without line breaks
            inline = self._extract_inline_after_label(
                text,
                ["Anschrift des Lieferanten"]
            )
            if inline:
                return self._clean_supplier_value(inline)
            # Prefer block after explicit info label
            block = self._extract_block_after_label(text, labels_after, max_lines=4)
            if block:
                return self._clean_supplier_value(block)
            # Common pattern: address follows the guarantee line
            block = self._extract_block_after_phrases(
                text,
                [
                    "Minimum duration of the guarantee offered by the supplier",
                    "Mindestdauer der vom Lieferanten angebotenen Garantie"
                ],
                max_lines=4
            )
            if block:
                return self._clean_supplier_value(block)
            # If label appears after the address, capture preceding lines
            block = self._extract_block_before_label(text, labels_before, max_lines=4)
            if block:
                return self._clean_supplier_value(block)
            # Fallback to labeled single-line extraction
            value = self._extract_labeled_value(text, labels_after + labels_before)
            if value and not self._looks_like_annotation(value):
                return self._clean_supplier_value(value)
        return ""

    def _extract_block_after_phrases(self, text: str, phrases: list[str], max_lines: int = 4) -> str:
        """Return a block of lines after a line containing any phrase."""
        lines = [line.strip() for line in text.splitlines() if line.strip()]
        lower_lines = [line.lower() for line in lines]
        for phrase in phrases:
            phrase_lower = phrase.lower()
            for i, line in enumerate(lower_lines):
                if phrase_lower in line:
                    collected = []
                    for j in range(i + 1, min(i + 1 + max_lines, len(lines))):
                        if re.match(r"^\d+\.", lines[j]):
                            break
                        if lines[j].startswith("("):
                            break
                        if self._looks_like_section_heading(lines[j]):
                            break
                        if self._looks_like_annotation(lines[j]):
                            continue
                        collected.append(lines[j])
                    if collected:
                        return " ".join(collected)
        return ""

    def _extract_inline_after_label(self, text: str, labels: list[str]) -> str:
        """Extract inline value after a label in a long text line."""
        for label in labels:
            pattern = r"\s+".join(map(re.escape, label.split()))
            match = re.search(
                rf"{pattern}\s*(?:\([a-z]\)\s*)*:?\s*(.+)",
                text,
                re.I | re.S
            )
            if match:
                value = match.group(1).strip()
                return value
        return ""

    def _extract_block_after_label(self, text: str, labels: list[str], max_lines: int = 4) -> str:
        """Return a block of lines after a label line."""
        lines = [line.strip() for line in text.splitlines() if line.strip()]
        lower_lines = [line.lower() for line in lines]
        for label in labels:
            label_lower = label.lower()
            for i, line in enumerate(lower_lines):
                if label_lower in line:
                    collected = []
                    for j in range(i + 1, min(i + 1 + max_lines, len(lines))):
                        if re.match(r"^\\([a-z]\\)\\s*$", lines[j], re.I):
                            break
                        if re.match(r"^\d+\.", lines[j]):
                            break
                        if lines[j].startswith("("):
                            break
                        if self._looks_like_section_heading(lines[j]):
                            break
                        collected.append(lines[j])
                    if collected:
                        return " ".join(collected)
        return ""

    def _extract_block_before_label(self, text: str, labels: list[str], max_lines: int = 4) -> str:
        """Return a block of lines before a label line."""
        lines = [line.strip() for line in text.splitlines() if line.strip()]
        lower_lines = [line.lower() for line in lines]
        for label in labels:
            label_lower = label.lower()
            for i, line in enumerate(lower_lines):
                if label_lower in line:
                    collected = []
                    start = max(0, i - max_lines)
                    for j in range(i - 1, start - 1, -1):
                        if re.match(r"^\d+\.", lines[j]):
                            break
                        if self._looks_like_section_heading(lines[j]):
                            break
                        if self._looks_like_annotation(lines[j]):
                            continue
                        collected.append(lines[j])
                    if collected:
                        return " ".join(reversed(collected))
        return ""

    def _looks_like_annotation(self, text: str) -> bool:
        stripped = text.strip()
        if not stripped:
            return True
        if re.fullmatch(r"(\\([a-z]\\)\\s*)+", stripped, re.I):
            return True
        if len(stripped) <= 2:
            return True
        return False

    def _looks_like_section_heading(self, text: str) -> bool:
        lower = text.lower()
        return (
            "product information sheet" in lower
            or "produktdatenblatt" in lower
            or "additional information" in lower
            or "repairability" in lower
        )

    def _clean_supplier_value(self, value: str) -> str:
        """Trim annotations and trailing sections from supplier value."""
        text = value.strip().replace("’", "'")
        # Remove known labels if included
        text = re.sub(
            r"^(supplier information|lieferanteninformation|anschrift des lieferanten|supplier's address|supplier address)\\s*",
            "",
            text,
            flags=re.I
        )
        # Remove trailing label artifacts if OCR placed them after the address
        text = re.sub(r"\bsupplier\s*'?s\s*address.*$", "", text, flags=re.I)
        text = re.sub(r"\banschrift des lieferanten.*$", "", text, flags=re.I)
        # Remove standalone annotation markers
        text = re.sub(r"\\s*(\\([a-z]\\)\\s*)+\\s*$", "", text, flags=re.I)
        # Cut off at section headings
        for marker in [
            "Produktdatenblatt",
            "Product information sheet",
            "Additional information",
            "Angaben zur Reparierbarkeit"
        ]:
            idx = text.lower().find(marker.lower())
            if idx != -1:
                text = text[:idx].strip()
        # Cut off when a new numbered section begins (common in these PDFs)
        text = re.sub(r"\d{1,2}\.\s+.+$", "", text).strip()
        # Insert spaces where OCR concatenates words/lines
        text = re.sub(r"([a-z])([A-Z])", r"\1 \2", text)
        text = re.sub(r"([A-Za-z])([0-9])", r"\1 \2", text)
        text = re.sub(r"([0-9])([A-Za-z])", r"\1 \2", text)
        # Collapse whitespace
        text = re.sub(r"\s+", " ", text).strip()
        return text

    
    def _extract_labeled_value(
        self,
        text: str,
        labels: list[str],
        value_pattern: Optional[str] = None
    ) -> str:
        """Find a label in text and return its value from same/next line."""
        if not text:
            return ""
        
        lines = [line.strip() for line in text.splitlines() if line.strip()]
        lower_lines = [line.lower() for line in lines]
        
        for label in labels:
            label_lower = label.lower()
            for i, line in enumerate(lower_lines):
                if label_lower in line:
                    original_line = lines[i]
                    # Try same-line "Label: value"
                    match = re.search(rf"{re.escape(label)}\s*[:\-]?\s*(.+)", original_line, re.I)
                    if match and match.group(1).strip():
                        candidate = match.group(1).strip()
                        if value_pattern:
                            val_match = re.search(value_pattern, candidate)
                            if val_match:
                                return val_match.group(0)
                        return candidate
                    
                    # Fallback to next line
                    if i + 1 < len(lines):
                        candidate = lines[i + 1].strip()
                        if value_pattern:
                            val_match = re.search(value_pattern, candidate)
                            if val_match:
                                return val_match.group(0)
                        return candidate
        
        return ""


# ============================================================================
# ENTRY POINT
# ============================================================================

def main():
    """Entry point"""
    try:
        scraper = Scraper()
        scraper.run()
    except Exception as e:
        logger.error(f"Fatal error: {e}", exc_info=True)
        raise


if __name__ == "__main__":
    main()
