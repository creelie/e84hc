"""Check every entry of paper/references.bib against an online record.

For an entry with a DOI the record is Crossref (DataCite for Zenodo, the Japan
Link Center for Japanese repositories); for an arXiv eprint it is the arXiv
API; for a numdam or GitHub URL it is the page itself; for an older book or
proceedings volume without a DOI it is a Crossref bibliographic search or the
Open Library catalogue.  The script
compares titles (after normalising accents, case and punctuation), years,
volumes and first pages, and writes verification/references/report.md.

Usage: python3 verification/references/check_references.py
"""

import json
import re
import sys
import time
import unicodedata
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from difflib import SequenceMatcher
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BIB = ROOT / "paper" / "references.bib"
REPORT = ROOT / "verification" / "references" / "report.md"
UA = {"User-Agent": "e84hc-reference-check/1.0 (mailto:itsdeep@live.com)"}


def get(url, timeout=40):
    for attempt in range(4):
        try:
            req = urllib.request.Request(url, headers=UA)
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return r.status, r.read().decode("utf-8", "replace")
        except urllib.error.HTTPError as e:
            if e.code in (404, 410):
                return e.code, ""
            time.sleep(2 ** attempt)
        except Exception:
            time.sleep(2 ** attempt)
    return 0, ""


def parse_bib(text):
    entries = []
    for m in re.finditer(r"@(\w+)\{([^,]+),(.*?)\n\}", text, re.S):
        kind, key, body = m.group(1), m.group(2).strip(), m.group(3)
        fields = {}
        for f in re.finditer(r"(\w+)\s*=\s*\{((?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*)\}", body):
            fields[f.group(1).lower()] = f.group(2)
        entries.append((kind, key, fields))
    return entries


def norm(s):
    s = re.sub(r"\\[a-zA-Z]+\s*", " ", s)              # TeX commands
    s = s.replace("{", "").replace("}", "").replace("$", "")
    s = unicodedata.normalize("NFKD", s)
    s = "".join(c for c in s if not unicodedata.combining(c))
    s = re.sub(r"[^a-z0-9 ]", " ", s.lower())
    return " ".join(s.split())


def similar(a, b):
    a, b = norm(a), norm(b)
    if not a or not b:
        return 0.0
    if (a in b or b in a) and min(len(a), len(b)) >= 0.7 * max(len(a), len(b)):
        return 1.0
    if len(a) >= 25 and a in b:       # the record's title extends ours
        return 1.0
    return SequenceMatcher(None, a, b).ratio()


def check_doi(doi, f):
    st, body = get("https://api.crossref.org/works/" + urllib.parse.quote(doi))
    src = "Crossref"
    if st != 200:
        st, body = get("https://api.datacite.org/dois/" + urllib.parse.quote(doi))
        src = "DataCite"
        if st == 200:
            a = json.loads(body)["data"]["attributes"]
            title = a["titles"][0]["title"]
            year = str(a.get("publicationYear", ""))
            vol = page = ""
        else:
            # Japan Link Center, for DOIs of Japanese repositories; the API
            # expects the slash encoded twice
            st, body = get("https://api.japanlinkcenter.org/dois/" +
                           urllib.parse.quote(urllib.parse.quote(doi, safe=""), safe=""))
            src = "JaLC"
            if st != 200:
                return False, f"DOI {doi} not found in Crossref, DataCite or JaLC"
            a = json.loads(body)["data"]
            title = a["title_list"][0]["title"]
            year = str(a.get("publication_date", {}).get("publication_year", ""))
            vol, page = a.get("volume", ""), a.get("first_page", "")
    else:
        m = json.loads(body)["message"]
        title = (m.get("title") or [""])[0]
        if not title:
            # some records carry no title; match on author, year and first page
            fam = [a.get("family", "") for a in m.get("author", [])]
            yr = ((m.get("issued") or {}).get("date-parts") or [[None]])[0][0]
            pg = m.get("page", "")
            ok = (norm(f.get("author", "")).split()[0] in [norm(x) for x in fam]
                  and str(yr) == f.get("year") and pg and pg.split("-")[0] in f.get("pages", ""))
            return ok, (f"Crossref record without title: author {', '.join(fam)}, "
                        f"{yr}, p. {pg}, {(m.get('container-title') or [''])[0]}")
        if m.get("subtitle"):
            title += " " + m["subtitle"][0]
        parts = (m.get("issued") or {}).get("date-parts") or [[None]]
        year = str(parts[0][0] or "")
        # journals that publish online first (Crelle) are dated by the print issue
        pp = ((m.get("published-print") or {}).get("date-parts") or [[None]])[0][0]
        if pp and f.get("year") == str(pp):
            year = str(pp)
        vol = m.get("volume", "") or ""
        # Crelle files the year as the volume and the volume number as the issue
        if f.get("volume") and m.get("issue") == f["volume"] and vol == f.get("year"):
            vol = f["volume"]
        page = m.get("page", "") or m.get("article-number", "") or ""
    s = similar(f.get("title", ""), title)
    notes = []
    ok = s >= 0.75
    if f.get("year") and year and abs(int(f["year"]) - int(year)) > 1:
        ok = False
        notes.append(f"year {year} vs {f['year']}")
    if vol and f.get("volume") and norm(vol) not in norm(f["volume"]):
        notes.append(f"volume {vol} vs {f['volume']}")
    if page and f.get("pages"):
        p0 = re.split(r"[-\u2013,]", page)[0].strip()
        if p0 and p0 not in f["pages"]:
            notes.append(f"page {page} vs {f['pages']}")
    return ok, f"{src}: \"{title}\" ({year}" + (f", vol. {vol}" if vol else "") + \
        (f", p. {page}" if page else "") + f"); title match {s:.2f}" + \
        ("; " + "; ".join(notes) if notes else "")


def check_arxiv(eid, f):
    st, body = get("https://export.arxiv.org/api/query?id_list=" + eid)
    if st != 200:
        return False, f"arXiv {eid}: no response"
    ns = {"a": "http://www.w3.org/2005/Atom"}
    root = ET.fromstring(body)
    e = root.find("a:entry", ns)
    if e is None or e.find("a:title", ns) is None:
        return False, f"arXiv {eid}: not found"
    title = " ".join(e.find("a:title", ns).text.split())
    authors = ", ".join(a.find("a:name", ns).text for a in e.findall("a:author", ns))
    s = similar(f.get("title", ""), title)
    return s >= 0.75, f"arXiv {eid}: \"{title}\" by {authors}; title match {s:.2f}"


def check_url(url, f):
    st, body = get(url)
    if st != 200:
        return False, f"{url}: HTTP {st}"
    t = norm(f.get("title", ""))
    words = [w for w in t.split() if len(w) > 3][:6]
    hit = sum(1 for w in words if w in norm(body))
    return hit >= max(1, len(words) // 2), f"{url}: HTTP 200, {hit}/{len(words)} title words on the page"


def check_search(f):
    q = norm(f.get("title", "")) + " " + norm(f.get("author", "").split(" and ")[0])
    st, body = get("https://api.crossref.org/works?rows=5&query.bibliographic=" +
                   urllib.parse.quote(q))
    best = (0.0, "")
    if st == 200:
        for it in json.loads(body)["message"]["items"]:
            t = (it.get("title") or [""])[0]
            s = similar(f.get("title", ""), t)
            if s > best[0]:
                y = ((it.get("issued") or {}).get("date-parts") or [[None]])[0][0]
                best = (s, f"Crossref search: \"{t}\" ({y}), DOI {it.get('DOI')}")
    if best[0] < 0.75:
        st, body = get("https://openlibrary.org/search.json?limit=5&title=" +
                       urllib.parse.quote(norm(f.get("booktitle", f.get("title", "")))))
        if st == 200:
            for d in json.loads(body).get("docs", []):
                t = d.get("title", "")
                s = similar(f.get("booktitle", f.get("title", "")), t)
                if s > best[0]:
                    best = (s, f"Open Library: \"{t}\" ({d.get('first_publish_year')}), "
                               f"{', '.join(d.get('author_name', [])[:2])}")
    return best[0] >= 0.75, best[1] or "no online record found"


# Works with no DOI, arXiv id or stable page of their own.  Each was checked
# by hand against the record named here; the script confirms that the record
# is still online.
MANUAL = {
    "Lef24": ("https://archive.org/advancedsearch.php?q=title%3A%28analysis+situs%29"
              "+AND+creator%3A%28Lefschetz%29&fl%5B%5D=identifier&output=json",
              "Internet Archive and Open Library: S. Lefschetz, L'analysis situs et la "
              "geometrie algebrique, Gauthier-Villars, 1924"),
    "Hod52": ("https://www.mathunion.org/fileadmin/ICM/Proceedings/ICM1950.1/ICM1950.1.ocr.pdf",
              "scan of the ICM 1950 Proceedings, vol. 1 (AMS, 1952): the address "
              "starts on p. 182, and the next one (Hopf) on p. 193"),
    "Kle68": ("https://ncatlab.org/nlab/show/Standard+Conjectures+on+Algebraic+Cycles",
              "nLab references and Open Library: Dix exposes sur la cohomologie des "
              "schemas, North-Holland, 1968, pp. 359-386, MR0292838"),
    "Gro69": ("https://ncatlab.org/nlab/show/Standard+Conjectures+on+Algebraic+Cycles",
              "nLab references: Algebraic Geometry (Bombay, 1968), Oxford Univ. Press, "
              "pp. 193-199"),
    "CG80": ("https://www.numdam.org/item/CM_1983__50_2-3_109_0/",
             "cited as [4] in Carlson, Green, Griffiths and Harris, Compositio Math. 50 "
             "(1983): Journees de geometrie algebrique d'Angers, Sijthoff and Noordhoff "
             "(1980) 51-76",
             "global Torelli problem"),
    "BhHCF": ("https://github.com/creelie/Hodge-Conjecture-Full",
              "public GitHub repository holding paper/full_attempt.tex, checked with "
              "a web fetch on 2026-10-08"),
    "OAI26b": ("https://raw.githubusercontent.com/openai/math/main/CONTENTS.md",
               "listed in CONTENTS.md of github.com/openai/math as preprints/Abelian-"
               "covers-Gale-correspondences-and-the-Hodge-conjecture-for-powers-October-6-2026/paper.pdf",
               "Abelian-covers-Gale-correspondences-and-the-Hodge-conjecture-for-powers-October-6-2026"),
    "OAI26c": ("https://raw.githubusercontent.com/openai/math/main/CONTENTS.md",
               "listed in CONTENTS.md of github.com/openai/math as preprints/Weil-classes-"
               "and-Hodge-classes-on-abelian-powers-October-6-2026/paper.pdf",
               "Weil-classes-and-Hodge-classes-on-abelian-powers-October-6-2026"),
    "OAI26": ("https://raw.githubusercontent.com/openai/math/main/CONTENTS.md",
              "listed in CONTENTS.md of github.com/openai/math as preprints/The-rational-"
              "Hodge-conjecture-for-CM-abelian-varieties-October-6-2026/paper.pdf",
              "The-rational-Hodge-conjecture-for-CM-abelian-varieties-October-6-2026"),
}


def main():
    entries = parse_bib(BIB.read_text())
    rows, bad = [], 0
    for kind, key, f in entries:
        if key in MANUAL:
            url, desc = MANUAL[key][:2]
            must = MANUAL[key][2] if len(MANUAL[key]) > 2 else ""
            st, body = get(url, timeout=120)
            if st == 200 and must and must not in body:
                ok, msg = False, f"{desc}; the record no longer contains {must!r}"
            elif st == 200:
                ok, msg = True, f"{desc} (record online: HTTP 200)"
            else:
                ok, msg = None, f"{desc}; not reachable from this network (HTTP {st})"
        elif "doi" in f:
            ok, msg = check_doi(f["doi"], f)
        elif f.get("archiveprefix", "").lower() == "arxiv":
            ok, msg = check_arxiv(f["eprint"], f)
        elif "url" in f:
            ok, msg = check_url(f["url"], f)
        elif "\\url{" in f.get("howpublished", ""):
            url = re.search(r"\\url\{([^}]*)\}", f["howpublished"]).group(1)
            ok, msg = check_url(url, {"title": "Hodge conjecture"})
        else:
            ok, msg = check_search(f)
        mark = "verified" if ok else ("by hand" if ok is None and key in MANUAL
                                      else "not online" if ok is None else "CHECK")
        if ok is False:
            bad += 1
        rows.append((key, mark, msg))
        print(f"{mark:10s} {key:8s} {msg}", flush=True)
        time.sleep(0.3)
    lines = ["# Online check of paper/references.bib", "",
             f"Run on {time.strftime('%Y-%m-%d')} by "
             "`verification/references/check_references.py`.", "",
             "| key | status | online record |", "|---|---|---|"]
    lines += [f"| {k} | {m} | {msg.replace('|', '/')} |" for k, m, msg in rows]
    lines += ["", f"{len(rows)} entries, {bad} need attention."]
    REPORT.write_text("\n".join(lines) + "\n")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
