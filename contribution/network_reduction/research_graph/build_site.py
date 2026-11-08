"""Package the checked-in graph and its source PDF for GitHub Pages.

Uses only the Python standard library. Does not replay mathematical proofs.
The explicit file list keeps unrelated repository files out of the website.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build(destination):
    graph = json.loads((HERE / 'GRAPH.json').read_text())
    preview = json.loads((HERE / 'PDF_PREVIEW.json').read_text())
    document = graph['documents'][0]
    assert digest(HERE.parent / 'NETWORK_REDUCTION.pdf') == document['pdf_sha256']
    assert digest(HERE.parent / 'REPORT.md') == document['sha256']
    assert preview['pdf_sha256'] == document['pdf_sha256']
    expected = (HERE / 'viewer_template.html').read_text()
    for marker, data in [('/*GRAPH_DATA*/', graph), ('/*PDF_DATA*/', preview)]:
        expected = expected.replace(marker, json.dumps(data, ensure_ascii=False).replace('<', r'\u003c'))
    expected = expected.replace('/*VIEWER_CODE*/', (HERE / 'viewer.js').read_text())
    assert (HERE / 'GRAPH.html').read_text() == expected, 'Rebuild GRAPH.html before publishing'
    validation = json.loads((HERE / 'VALIDATION.json').read_text())
    assert validation['status'] == 'PASS'
    assert len(preview['pages']) == document['page_count']
    assert not destination.exists() or not any(destination.iterdir()), 'Use an empty output directory'
    viewer = destination / 'research_graph'
    (viewer / 'pdf_pages').mkdir(parents=True)
    for name in ['GRAPH.html', 'GRAPH.json', 'GRAPH.txt', 'VALIDATION.json', 'PDF_PREVIEW.json']:
        shutil.copyfile(HERE / name, viewer / name)
    for page in preview['pages']:
        relative = Path(page['image'])
        assert relative.parts == ('pdf_pages', 'page-%02d.png' % page['number'])
        shutil.copyfile(HERE / relative, viewer / relative)
    shutil.copyfile(HERE.parent / 'NETWORK_REDUCTION.pdf', destination / 'NETWORK_REDUCTION.pdf')
    (destination / '.nojekyll').write_text('')
    (destination / 'index.html').write_text('''<!doctype html>
<html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<meta http-equiv="refresh" content="0;url=research_graph/GRAPH.html">
<title>Research graph — controller reduction and repair</title>
<p><a href="research_graph/GRAPH.html">Open the interactive research graph and PDF</a></p>
</html>
''')
    print('Packaged graph, %s PDF page images, and the source PDF in %s' % (len(preview['pages']), destination))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    build(parser.parse_args().output)
