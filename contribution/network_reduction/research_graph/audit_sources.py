"""Check source pointers against the pinned Markdown, PDF and preview.

This checks source identity, locations and equation bindings. It does not
prove the semantic interpretation of graph claims or replay Lean proofs.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

import pymupdf as fitz
from pdf_preview import display_equations, equation_panels, equation_rectangles, source_rectangles

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit():
    graph = json.loads((HERE/'GRAPH.json').read_text())
    preview = json.loads((HERE/'PDF_PREVIEW.json').read_text())
    source = graph['documents'][0]
    assert digest(ROOT/source['path']) == source['sha256']
    assert digest(ROOT/source['pdf_path']) == source['pdf_sha256'] == preview['pdf_sha256']
    lines = (ROOT/source['path']).read_text().splitlines()
    page_for_line, page = [], 1
    for line in lines:
        page_for_line.append(page)
        if line.strip() == '<!-- pagebreak -->':
            page += 1
    with fitz.open(ROOT/source['pdf_path']) as pdf:
        assert len(pdf) == source['page_count'] == len(preview['pages'])
        words = {i+1: p.get_text('words', sort=True) for i,p in enumerate(pdf)}
        panels = {i+1: equation_panels(p) for i,p in enumerate(pdf)}
        # Verify every rendered equation against the full Markdown, in order,
        # independently of which graph objects happen to refer to it.
        expected = display_equations('\n'.join(lines))
        actual = [p['expression'] for entries in panels.values() for p in entries]
        assert actual == expected, 'PDF ActualText differs from Markdown equation sequence'
        assert preview['equation_panels'] == {str(k):v for k,v in panels.items() if v}
        rows = []
        for node in graph['nodes']:
            s = node['source']; lo,hi = s['line_start'],s['line_end']
            assert s['passage'] == '\n'.join(lines[lo-1:hi]), node['id']
            assert s['pdf_pages'] == sorted(set(page_for_line[lo-1:hi])), node['id']
            text = source_rectangles(s, words)
            math = equation_rectangles(s, panels)
            assert preview['highlights'][node['id']] == text
            assert preview['equation_highlights'][node['id']] == math
            matched = sorted({int(p) for p in text} | {int(p) for p in math})
            assert matched and s['pdf_pages'][0] in matched, 'Empty landing page: '+node['id']
            for mapping in (text, math):
                for number, boxes in mapping.items():
                    page_rect = pdf[int(number)-1].rect
                    assert all(0 <= x0 < x1 <= page_rect.width and 0 <= y0 < y1 <= page_rect.height
                               for x0,y0,x1,y1 in boxes), node['id']
            rows.append(dict(id=node['id'], lines=[lo,hi], pages=s['pdf_pages'],
                             text_rectangles=sum(map(len,text.values())),
                             equation_rectangles=sum(map(len,math.values()))))
        by_id = {n['id']:n for n in graph['nodes']}
        assert by_id['C14']['source']['pdf_pages'] == [24]
        assert 'Square roots can yield irrational' in by_id['L1']['source']['passage']
        assert 'original unrepaired graph used 11' in by_id['L3']['source']['passage']
        assert 'operator has three checked laws' in by_id['U19']['source']['passage']
        controls = []
        for name, operation in [
            ('partial equation rejected', lambda: display_equations('$$\nx=y')),
            ('unrelated equation rejected', lambda: equation_rectangles(
                {'passage':'$$\nnot_the_document_equation\n$$','pdf_pages':[2]}, panels)),
            ('equation on wrong page rejected', lambda: equation_rectangles(
                {'passage':'$$\n'+panels[2][0]['expression']+'\n$$','pdf_pages':[1]}, panels)),
        ]:
            try:
                operation()
            except AssertionError:
                controls.append(name)
            else:
                raise AssertionError('Bad mapping accepted: '+name)
    report = dict(status='PASS', timestamp_utc=datetime.now(timezone.utc).isoformat(),
                  graph_sha256=digest(HERE/'GRAPH.json'), pdf_sha256=source['pdf_sha256'],
                  preview_sha256=digest(HERE/'PDF_PREVIEW.json'),
                  nodes_checked=len(rows), pdf_equations_checked=len(expected), nodes=rows,
                  negative_controls=controls,
                  corrected_examples={'C14':'Quality gate now opens on page 24.',
                      'L1':'Points to the actual irrational-parameter boundary on page 16.',
                      'U19':'Includes the complete paragraph introducing all three operator laws.',
                      'L3':'Includes the comparison with 11 original ReLUs, not a truncated paragraph.'},
                  scope='Source and location checks. Prose uses matched token runs; equations use exact embedded ActualText and checked panel geometry. Not a semantic proof of extraction or a new Lean run.')
    (HERE/'SOURCE_POINTER_CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS: {len(rows)} source pointers, {len(expected)} PDF equations, {len(controls)} negative controls.')


if __name__ == '__main__':
    audit()
