"""Browser regression checks for graph interaction and PDF source selection.

Requires Playwright and a local Chromium browser. No web server is required.
"""
import argparse
import json
from pathlib import Path

from playwright.sync_api import sync_playwright

HERE = Path(__file__).resolve().parent
GRAPH = json.loads((HERE / "GRAPH.json").read_text())


def node_ids(page):
    return set(page.locator("[data-node]").evaluate_all(
        "nodes => nodes.map(n => n.dataset.node)"))


def edge_ids(page):
    return set(page.locator("[data-edge]").evaluate_all(
        "edges => edges.map(e => e.dataset.edge)"))


def pdf_state(page):
    page.wait_for_function(
        'document.querySelector("#pdf-image")?.naturalWidth > 0')
    return page.evaluate("""() => ({
        sources: document.querySelector("#pdf-panel").dataset.sourceIds,
        page: document.querySelector("#pdf-pages").value,
        marks: document.querySelector(".pdf-highlights").innerHTML,
        scroll: document.querySelector("#pdf-scroll").scrollTop,
        image: document.querySelector("#pdf-image").src
    })""")


def position(page, node):
    return page.locator('[data-node="%s"]' % node).evaluate(
        "n => { const m=n.transform.baseVal.getItem(0).matrix; return {x:m.e,y:m.f}; }")


def drag_node(page, node, dx=35, dy=70):
    element = page.locator('[data-node="%s"]' % node)
    element.scroll_into_view_if_needed()
    box = element.bounding_box()
    x, y = box["x"] + box["width"] / 2, box["y"] + box["height"] / 2
    page.mouse.move(x, y)
    page.mouse.down()
    page.mouse.move(x + dx, y + dy, steps=12)
    page.mouse.up()


def click_curve(page, edge_id):
    """Click a visible part of the actual SVG curve, not an inspector shortcut."""
    group = page.locator('[data-edge="%s"]' % edge_id)
    group.scroll_into_view_if_needed()
    point = group.evaluate("""g => {
      const path=g.querySelector(".edge-hit"), length=path.getTotalLength();
      const canvas=document.querySelector("#canvas").getBoundingClientRect();
      for(let i=1;i<20;i++){
        const p=path.getPointAtLength(length*i/20).matrixTransform(path.getScreenCTM());
        if(p.x<canvas.left+5 || p.x>canvas.right-5 || p.y<canvas.top+5 || p.y>canvas.bottom-5) continue;
        if(document.elementFromPoint(p.x,p.y)?.closest("[data-edge]")===g) return {x:p.x,y:p.y};
      }
      return null;
    }""")
    assert point, "No exposed clickable curve for " + edge_id
    page.mouse.click(point["x"], point["y"])


def check_node_context(page, node_id):
    expected_nodes, expected_edges = {node_id}, set()
    for edge in GRAPH["edges"]:
        if node_id in (edge["source"], edge["target"]):
            expected_nodes.update([edge["source"], edge["target"]])
            expected_edges.add(edge["id"])
    for joint in GRAPH["joint_inferences"]:
        members = joint["premises"] + joint["evidence"] + joint["conclusions"]
        if node_id in [joint["id"]] + members:
            expected_nodes.update([joint["id"]] + members)
            for kind, field in [("premise", "premises"), ("evidence", "evidence"), ("conclusion", "conclusions")]:
                expected_edges.update(joint["id"] + ":" + kind + ":" + item for item in joint[field])
    assert node_ids(page) == expected_nodes
    assert edge_ids(page) == expected_edges


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--browser", default="/Applications/Google Chrome.app/Contents/MacOS/Google Chrome")
    parser.add_argument("--output", type=Path, default=HERE.parents[1] / ".build" / "graph-viewer-results")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    checks, errors = [], []
    with sync_playwright() as p:
        browser = p.chromium.launch(executable_path=args.browser, headless=True)
        page = browser.new_page(viewport={"width": 1600, "height": 1100})
        page.on("pageerror", lambda error: errors.append(str(error)))
        page.goto((HERE / "GRAPH.html").as_uri())
        initial = pdf_state(page)
        assert initial["sources"] == "Q5" and initial["marks"]
        check_node_context(page, "Q5")
        checks.append("Initial node isolates its context and highlights the source PDF")

        before = position(page, "Q5")
        paths = page.locator(".edge").evaluate_all("paths=>paths.map(p=>p.getAttribute('d'))")
        factor = page.locator("#graph").evaluate("g=>g.getScreenCTM().a")
        drag_node(page, "Q5")
        after = position(page, "Q5")
        assert abs(after["x"] - before["x"] - 35 / factor) < 1
        assert abs(after["y"] - before["y"] - 70 / factor) < 1
        assert paths != page.locator(".edge").evaluate_all("paths=>paths.map(p=>p.getAttribute('d'))")
        assert pdf_state(page) == initial
        assert page.locator("#graph").get_attribute("data-selection-id") == "Q5"
        checks.append("Dragging moves the node and its curves without changing selection or PDF")

        page.locator("#plus").click()
        before = position(page, "Q5")
        factor = page.locator("#graph").evaluate("g=>g.getScreenCTM().a")
        drag_node(page, "Q5", 20, 30)
        after = position(page, "Q5")
        assert abs(after["x"] - before["x"] - 20 / factor) < 1, (before, after, factor)
        assert abs(after["y"] - before["y"] - 30 / factor) < 1
        assert pdf_state(page) == initial
        page.locator("#labels").check()
        page.locator("#fit").click()
        assert pdf_state(page) == initial
        checks.append("Dragging remains accurate under zoom; zoom and labels preserve PDF")

        saved = position(page, "Q5")
        page.reload()
        assert position(page, "Q5") == saved
        pdf_state(page)
        checks.append("Manual positions survive reload")

        click_curve(page, "R034")
        assert edge_ids(page) == {"R034"}
        assert node_ids(page) == {"Q5", "A6"}
        assert page.locator('[data-edge="R034"]').get_attribute("aria-pressed") == "true"
        assert page.locator("#graph").get_attribute("data-selection-type") == "edge"
        edge_pdf = pdf_state(page)
        assert set(edge_pdf["sources"].split(",")) == {"Q5", "A6"}
        page.screenshot(path=str(args.output / "edge-selection.png"), full_page=True)
        drag_node(page, "A6", 10, 50)
        assert pdf_state(page) == edge_pdf
        assert edge_ids(page) == {"R034"}
        checks.append("Clicking a curve isolates its endpoints; dragging preserves edge/PDF selection")

        click_curve(page, "R034")
        assert page.locator("#graph").get_attribute("data-selection-id") == ""
        assert len(edge_ids(page)) > 1
        assert pdf_state(page) == edge_pdf
        click_curve(page, "R034")
        assert edge_ids(page) == {"R034"}
        page.keyboard.press("Enter")
        assert page.locator("#graph").get_attribute("data-selection-id") == ""
        page.keyboard.press("Enter")
        assert edge_ids(page) == {"R034"}
        checks.append("Mouse and keyboard toggle a selected edge without losing the PDF passage")

        page.locator("#show-all").click()
        assert len(node_ids(page)) > 2
        assert pdf_state(page) == edge_pdf
        page.locator('[data-node="Q6"]').click()
        check_node_context(page, "Q6")
        assert pdf_state(page)["sources"] == "Q6"
        assert page.evaluate("document.activeElement.dataset.node") == "Q6"
        before = position(page, "Q6")
        page.keyboard.press("Alt+ArrowRight")
        assert position(page, "Q6")["x"] == before["x"] + 10
        page.keyboard.press("Enter")
        assert page.locator("#graph").get_attribute("data-selection-id") == ""
        assert page.evaluate("document.activeElement.dataset.node") == "Q6"
        page.keyboard.press("Enter")
        assert page.locator("#graph").get_attribute("data-selection-id") == "Q6"
        checks.append("Mouse and keyboard node selection work; keyboard focus and movement survive redraw")

        node_pdf = pdf_state(page)
        page.locator('[data-node="Q6"]').click()
        assert page.locator("#graph").get_attribute("data-selection-id") == ""
        assert pdf_state(page) == node_pdf
        page.locator('[data-node="Q6"]').click()
        assert page.locator("#graph").get_attribute("data-selection-id") == "Q6"
        # The padded top-left corner is outside every SVG object and curve.
        page.locator("#canvas").click(position={"x": 3, "y": 3})
        assert page.locator("#graph").get_attribute("data-selection-id") == ""
        assert pdf_state(page) == node_pdf
        checks.append("Clicking a selected node or the background deselects while keeping its PDF passage")

        page.locator("#branch").select_option("robustness")
        click_curve(page, "J01:premise:A0")
        j = GRAPH["joint_inferences"][0]
        assert node_ids(page) == set([j["id"]] + j["premises"] + j["evidence"] + j["conclusions"])
        assert len(edge_ids(page)) == len(j["premises"] + j["evidence"] + j["conclusions"])
        joint_pdf = pdf_state(page)
        assert set(joint_pdf["sources"].split(",")) == node_ids(page) - {"J01"}
        page.screenshot(path=str(args.output / "joint-selection.png"), full_page=True)
        page.keyboard.press("Escape")
        assert page.locator("#graph").get_attribute("data-selection-id") == ""
        assert pdf_state(page) == joint_pdf
        checks.append("Joint edge selection retains every premise/evidence/conclusion; Escape preserves PDF")

        if page.locator("#pdf-pages option").count() > 1:
            page.locator("#pdf-pages").select_option(index=1)
            new_pdf = pdf_state(page)
            page.locator("#reset-layout").click()
            assert pdf_state(page) == new_pdf
        assert page.evaluate("Object.keys(manualPositions).length") == 0
        checks.append("PDF page navigation and reset positions keep the source selection")

        page.locator("#branch").select_option("rmsprop")
        page.locator('[data-node="Q5"]').click()
        assert position(page, "Q5") == {"x": 24, "y": 58}
        page.locator("#search").fill("no-matching-object-987654321")
        assert node_ids(page) == set()
        page.locator("#reset").click()
        assert len(node_ids(page)) > 0
        checks.append("Reset restores automatic layout; empty search and recovery work")

        for width in [1000, 600, 390]:
            page.set_viewport_size({"width": width, "height": 900})
            page.locator("#fit").click()
            assert page.locator("#canvas").bounding_box()["width"] <= width
            assert page.locator("#pdf-scroll").bounding_box()["height"] > 100
            assert page.evaluate("document.documentElement.scrollWidth <= innerWidth")
        page.screenshot(path=str(args.output / "narrow.png"), full_page=True)
        checks.append("Graph and PDF remain usable at 1000, 600 and 390px viewport widths")
        assert not errors, errors
        browser.close()
    result = {"status": "PASS", "checks": checks, "browser_errors": errors}
    (args.output / "interaction_checks.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
