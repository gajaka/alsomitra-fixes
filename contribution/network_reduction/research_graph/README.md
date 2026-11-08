# Interactive research graph

Open the [published graph and PDF viewer](https://gajaka.github.io/alsomitra-fixes/)
directly in a browser. No installation is needed.

Open [GRAPH.html](GRAPH.html) in a browser. It works directly from the local
filesystem; no server or network connection is needed. Keep the
`pdf_pages/` directory beside the HTML file.

The viewer connects the structured reading of the network-reduction guide
to its source PDF. The exported graph contains 99 objects, 102 typed
relations, and 17 joint inferences. The initial view is **Whole document**, with
all objects visible and no object or relation selected. The inspector and PDF
show the document overview.

## Explore and arrange

- **Drag an object** to move it. Its connections follow it. Moving an object
  preserves the selected object or relation, the PDF page, and its highlights.
  Manual positions are saved in this browser when local storage is available.
- **Click an object** to show only that object, its immediate connections,
  and the connected objects. The inspector explains the object and the PDF
  preview highlights its recorded source passage.
- **Click a connection** to show that relation and its endpoints. The inspector
  explains the relation; the PDF highlights the endpoints' source passages.
  The selected relation is orange.
- **Joint inferences retain the complete bundle:** selecting a joint node,
  one of its connections, or an involved object keeps all premises, evidence,
  and conclusions of the relevant inference visible. Required premises are
  not presented as independent alternatives.
- **Click the selected object or connection again**, click the empty graph
  background, or use **Show branch** / **Escape** to deselect and restore the
  current branch overview while
  keeping the PDF selection. Choose **Whole document** to browse the full graph.
- **Reset positions** restores the automatic layout and clears saved positions
  across every branch. A status message confirms the reset; the selected object
  or relation and PDF passage stay selected. **Fit graph**, **+**, and **−**
  control the view.
- Changing **Branch** updates the graph, inspector and PDF highlights together.
  The overview highlights source passages of the matching branch objects;
  selecting an object or relation narrows the source selection. Search also
  refreshes the source context. An empty search result clears old highlights
  and page controls instead of retaining an unrelated passage.
- Use **Tab** to focus objects and connections and **Enter** or **Space** to
  select or deselect them. **Alt + arrow** moves a focused object; add **Shift** for a
  larger step.

Only the display is filtered. The JSON export retains every object and
relation. Layout columns group object types; they do not claim a chronological
discovery order.

## PDF source selection

The embedded preview uses images rendered from the original PDF. Prose
highlights match normalized runs of at least five tokens from the recorded
source passage, restricted to its recorded PDF pages. Display equations use
their exact embedded LaTeX `ActualText` and the bounds of their vector panels,
cross-checked against PDF drawing extraction. This mapping recognizes the
pinned document renderer's format and rejects unsupported formats or missing
equations; it is not a general PDF equation recognizer. The preview scrolls to
the first match. Its page selector visits the current selection's source pages.

These highlights are a reading aid. A relation reconstructed during extraction
may not appear as one sentence in the PDF; selecting it shows the connected
objects' passages. If no exact token run is found, the viewer shows the
recorded page and explicitly reports that no text or equation match was found.
**Open original PDF** opens the source document at the displayed page.

The [source-pointer audit](SOURCE_POINTER_CHECKS.json) checks all 99 records
against the exact Markdown and PDF, including all 60 display equations in the
document. It also records corrections to incomplete or misplaced source spans.
This verifies source identity and locations; it does not prove every graph
interpretation. To repeat it in the document-tools environment:

```sh
contribution/.build/document-tools/bin/python contribution/network_reduction/research_graph/audit_sources.py
```

## Source files and rebuilding

- `build_graph.py`: document-specific records, validation, and generated exports.
- `viewer_template.html` and `viewer.js`: layout and interaction logic.
- `pdf_preview.py`: rendered pages and source highlight coordinates.
- `GRAPH.json` / `GRAPH.txt`: structured and text exports.
- `PDF_PREVIEW.json` / `pdf_pages/`: preview metadata and rendered source pages.
- `VALIDATION.json`: structural and saved-evidence checks.

From the repository root, use the existing document-tools environment:

```sh
contribution/.build/document-tools/bin/python contribution/network_reduction/research_graph/build_graph.py
```

For another environment, the builder requires Python and PyMuPDF. The source
PDF and report are pinned by hashes; changing the source document requires
reviewing the extraction and its source bindings.

## Browser verification

The [saved interaction checks](INTERACTION_CHECKS.json) record 18 passing
scenarios, including selecting and deselecting both nodes and connections
while preserving the source PDF passage, synchronizing all branches with their
sources, and resetting saved positions across branches and reloads.
Every node's source pages and displayed text/equation marks are exercised.
The record includes the tested HTML hash. This is browser behavior validation,
separate from the mathematical proof receipts.

The interaction checks use Playwright with a local Chrome installation.
From the repository root:

```sh
python3 -m venv contribution/.build/graph-viewer-tools
contribution/.build/graph-viewer-tools/bin/python -m pip install playwright==1.60.0
contribution/.build/graph-viewer-tools/bin/python contribution/network_reduction/research_graph/test_viewer.py
```

Use `--browser /path/to/chromium` for another Chromium installation.
The checks exercise actual mouse clicks on SVG curves, dragging at different
zoom levels, node and edge isolation, full joint-premise visibility, position
persistence, keyboard operation, PDF selection preservation, and narrow
viewports. Screenshots and `interaction_checks.json` are written under
`contribution/.build/graph-viewer-results/`.

Graph validation checks source bindings and structural consistency. It does
not replay Lean proofs or establish the semantic correctness of the extraction.

## GitHub Pages

The `Publish research graph` workflow packages only the viewer, its exported
graph, the 26 preview images, and the source PDF. It checks that the generated
HTML matches its sources and that the PDF and report hashes match the graph.
It publishes relevant updates from `main`, or can be run manually in Actions.

The repository's **Settings → Pages → Build and deployment → Source** must be
set to **GitHub Actions**. The deployment uses GitHub's built-in workflow token;
no personal token is stored in the repository.

To inspect the same website package locally, choose an empty directory:

```sh
python3 contribution/network_reduction/research_graph/build_site.py --output contribution/.build/research-graph-site
python3 -m http.server 8091 --bind 127.0.0.1 --directory contribution/.build/research-graph-site
```

Then open `http://127.0.0.1:8091/`. Packaging does not rebuild the extraction
or rerun its mathematical proofs.
