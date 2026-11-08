"""Locate prose and vector equations in this source-bound document.

Highlights are a reading aid, not a semantic proof of the extracted relationship.
Equation mapping recognizes the pinned build_report.py MathPanel stream format;
it fails closed for an unrecognized format instead of estimating a location.
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


def display_equations(passage):
    equations, lines = [], None
    for line in passage.splitlines():
        if line.strip() == '$$':
            if lines is None:
                lines = []
            else:
                equations.append(' '.join(' '.join(lines).split()))
                lines = None
        elif lines is not None:
            lines.append(line)
    assert lines is None, 'Source passage cuts a display equation'
    return equations


def equation_panels(page):
    # MathPanel draws a rounded panel immediately before its ActualText span.
    # Parse that exact emitted form, then cross-check its rectangle against
    # MuPDF's independent drawing extraction. Other boxes are not equations.
    number = r'[-+]?(?:\d*\.\d+|\d+)(?:[eE][-+]?\d+)?'
    rgb = rf'{number}\s+{number}\s+{number}'
    pattern = re.compile(
        rf'\bq\s+1 0 0 1 ({number}) ({number}) cm\s+'
        rf'{rgb} rg\s+{rgb} RG\s+{number} w\s+n\s+'
        r'(?P<path>.*?)\s+B\*\s+/Span\s+<<\s*/ActualText\s+'
        r'<(?P<text>[0-9a-fA-F]+)>\s*>>\s*BDC', re.S)
    stream = page.read_contents().decode('latin1')
    matches = list(pattern.finditer(stream))
    assert len(matches) == stream.count('/ActualText'), 'Unrecognized equation panel format'
    drawings = [d['rect'] for d in page.get_drawings() if d['type'] == 'fs']
    panels = []
    for match in matches:
        points = []
        for line in match['path'].strip().splitlines():
            parts = line.split()
            assert parts[-1] in ('m', 'l', 'c', 'h'), 'Unexpected panel path operator'
            assert len(parts)-1 == {'m':2, 'l':2, 'c':6, 'h':0}[parts[-1]]
            points.extend(zip(map(float, parts[:-1:2]), map(float, parts[1:-1:2])))
        dx, dy = float(match[1]), float(match[2])
        xs, ys = zip(*points)
        rect = fitz.Rect(min(xs)+dx, min(ys)+dy, max(xs)+dx, max(ys)+dy) * page.transformation_matrix
        assert any(max(abs(a-b) for a,b in zip(rect, drawn)) < .02 for drawn in drawings), 'Equation panel bounds disagree'
        text = bytes.fromhex(match['text']).decode('utf-16')
        panels.append(dict(expression=' '.join(text.split()), rect=[round(v, 2) for v in rect]))
    return panels


def equation_rectangles(source, panels):
    rectangles = {}
    for expression in set(display_equations(source['passage'])):
        matches = [(page, panel) for page in source['pdf_pages']
                   for panel in panels[page] if panel['expression'] == expression]
        assert matches, 'No exact ActualText match for source equation: ' + expression
        for page, panel in matches:
            rectangles.setdefault(str(page), []).append(panel['rect'])
    return {page: sorted(boxes, key=lambda box:(box[1], box[0]))
            for page, boxes in sorted(rectangles.items(), key=lambda item:int(item[0]))}


def source_rectangles(source, page_words):
    prose = re.sub(r'(?ms)^\$\$\s*\n.*?^\$\$\s*$', '', source['passage'])
    needle = tokens(prose)
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
    pages, page_words, panels = [], {}, {}
    with fitz.open(pdf_path) as document:
        for page_index, page in enumerate(document):
            number = page_index + 1
            image = assets / ('page-%02d.png' % number)
            if not cached or not image.exists():
                page.get_pixmap(matrix=fitz.Matrix(1.5, 1.5), alpha=False).save(image)
            pages.append(dict(number=number, width=page.rect.width, height=page.rect.height,
                              image=str(image.relative_to(destination))))
            page_words[number] = page.get_text('words', sort=True)
            panels[number] = equation_panels(page)
    stamp.write_text(checksum + '\n')
    data = dict(pdf_sha256=checksum, pages=pages,
        highlights={n['id']: source_rectangles(n['source'], page_words)
                    for n in graph['nodes'] if n.get('source')},
        equation_highlights={n['id']: equation_rectangles(n['source'], panels)
                             for n in graph['nodes'] if n.get('source')},
        equation_panels={str(page): items for page, items in panels.items() if items},
        method='Prose: exact normalized runs of at least five tokens. Equations: exact ActualText matches and verified vector panel bounds. Both are restricted to recorded source pages.')
    (destination / 'PDF_PREVIEW.json').write_text(json.dumps(data, indent=2) + '\n')
    return data
