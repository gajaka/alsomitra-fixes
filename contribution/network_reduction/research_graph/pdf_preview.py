"""Render the source PDF and locate exact token runs for selection highlights.

Highlights are a reading aid, not a semantic proof of the extracted relationship.
Requires the project's existing document-tools environment (PyMuPDF).
"""
import difflib
import hashlib
import json
from pathlib import Path
import re
import unicodedata

import pymupdf as fitz


def tokens(text):
    return re.findall(r'\w+', unicodedata.normalize('NFKC', text).lower())


def source_rectangles(source, page_words):
    needle = tokens(source['passage'])
    haystack, locations = [], []
    for page in source['pdf_pages']:
        for word in page_words[page]:
            for token in tokens(word[4]):
                haystack.append(token)
                locations.append((page, word))
    selected = {}
    for match in difflib.SequenceMatcher(None, needle, haystack, autojunk=False).get_matching_blocks():
        # Short common phrases alone are insufficient to mark a source location.
        if match.size < 5:
            continue
        for index in range(match.b, match.b + match.size):
            page, word = locations[index]
            selected.setdefault(page, {})[tuple(word[:4])] = word
    rectangles = {}
    for page, words in selected.items():
        lines = {}
        for word in words.values():
            lines.setdefault((word[5], word[6]), []).append(word)
        merged = []
        for line in lines.values():
            for word in sorted(line, key=lambda w: w[0]):
                box = list(word[:4])
                if merged and abs(merged[-1][1] - box[1]) < 2 and 0 <= box[0] - merged[-1][2] < 14:
                    merged[-1][2] = box[2]
                    merged[-1][3] = max(merged[-1][3], box[3])
                else:
                    merged.append(box)
        rectangles[str(page)] = [[round(v, 2) for v in box] for box in merged]
    return rectangles


def build_pdf_preview(pdf_path, graph, destination):
    destination = Path(destination)
    assets = destination / 'pdf_pages'
    assets.mkdir(exist_ok=True)
    checksum = hashlib.sha256(Path(pdf_path).read_bytes()).hexdigest()
    stamp = assets / 'source.sha256'
    cached = stamp.exists() and stamp.read_text().strip() == checksum
    pages, page_words = [], {}
    with fitz.open(pdf_path) as document:
        for page_index, page in enumerate(document):
            number = page_index + 1
            image = assets / ('page-%02d.png' % number)
            if not cached or not image.exists():
                page.get_pixmap(matrix=fitz.Matrix(1.5, 1.5), alpha=False).save(image)
            pages.append(dict(number=number, width=page.rect.width, height=page.rect.height,
                              image=str(image.relative_to(destination))))
            page_words[number] = page.get_text('words', sort=True)
    stamp.write_text(checksum + '\n')
    data = dict(pdf_sha256=checksum, pages=pages,
        highlights={n['id']: source_rectangles(n['source'], page_words)
                    for n in graph['nodes'] if n.get('source')},
        method='Exact normalized token runs of at least five tokens, restricted to recorded source pages.')
    (destination / 'PDF_PREVIEW.json').write_text(json.dumps(data, indent=2) + '\n')
    return data
