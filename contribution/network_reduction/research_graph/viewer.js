const colors = {goal:'#24576f',question:'#246ca6',assumption:'#7d5ca4',hypothesis:'#976177',construction:'#2c7781',insight:'#2d805b',invariant:'#17675a',counterexample:'#ba4d34',limitation:'#8c663c',evidence:'#8c761a',joint_inference:'#4d5b68'};
const $ = id => document.getElementById(id);
const esc = value => String(value).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const byId = new Map([...DATA.nodes, ...DATA.joint_inferences].map(n => [n.id, n]));
const edges = DATA.edges.map(e => ({id:e.id, a:e.source, b:e.target, label:e.relation,
  kind:e.relation === 'answers' ? 'answer' : 'context', record:e}));
for (const j of DATA.joint_inferences) {
  for (const a of j.premises) edges.push({id:`${j.id}:premise:${a}`,a,b:j.id,label:'required premise',kind:'premise',joint:j.id});
  for (const a of j.evidence) edges.push({id:`${j.id}:evidence:${a}`,a,b:j.id,label:'evidence',kind:'evidence',joint:j.id});
  for (const b of j.conclusions) edges.push({id:`${j.id}:conclusion:${b}`,a:j.id,b,label:'conclusion',kind:'conclusion',joint:j.id});
}
const edgeById = new Map(edges.map(e => [e.id, e]));
const layoutKey = 'research-graph-layout-v1:' + DATA.documents[0].pdf_sha256;
let manualPositions = {};
try {
  const saved = JSON.parse(localStorage.getItem(layoutKey) || '{}');
  for (const [id, p] of Object.entries(saved)) {
    if (byId.has(id) && Number.isFinite(p.x) && Number.isFinite(p.y) && p.x >= 0 && p.y >= 40 && p.x < 100000 && p.y < 100000) manualPositions[id] = p;
  }
} catch (_) { /* Local layout persistence is optional. */ }
let selection = null, scale = .8, positions = new Map(), nodeElements = new Map(), drawnEdges = [];
let viewWidth = 1500, viewHeight = 700, viewX = 0, viewY = 0;
let visibleNodes = new Set(), drag = null, sourceIds = [], sourcePages = [], pdfPage = 1, pdfGeneration = 0;

function savePositions() {
  try { localStorage.setItem(layoutKey, JSON.stringify(manualPositions)); } catch (_) {}
}
function ref(id) { return `<button class="ref" data-id="${esc(id)}">${esc(id)}</button>`; }
function bindRefs() {
  document.querySelectorAll('[data-id]').forEach(b => b.onclick = () => toggleSelection('node', b.dataset.id));
  document.querySelectorAll('[data-edge-ref]').forEach(b => b.onclick = () => toggleSelection('edge', b.dataset.edgeRef));
}
function jointMembers(j) { return [...j.premises, ...j.evidence, ...j.conclusions]; }
function selectedScope() {
  if (!selection) return null;
  const nodeIds = new Set(), edgeIds = new Set();
  const addEdge = e => { edgeIds.add(e.id); nodeIds.add(e.a); nodeIds.add(e.b); };
  const addJoint = id => edges.filter(e => e.joint === id).forEach(addEdge);
  if (selection.type === 'edge') {
    const edge = edgeById.get(selection.id);
    if (edge.joint) addJoint(edge.joint); else addEdge(edge);
  } else {
    nodeIds.add(selection.id);
    edges.filter(e => e.a === selection.id || e.b === selection.id).forEach(addEdge);
    for (const j of DATA.joint_inferences) {
      if (j.id === selection.id || jointMembers(j).includes(selection.id)) addJoint(j.id);
    }
  }
  return {nodeIds, edgeIds};
}
function branchScope() {
  const branch = $('branch').value, query = $('search').value.trim().toLowerCase();
  let base = DATA.nodes.filter(n => (branch === 'all' || n.case === branch) && (!query || JSON.stringify(n).toLowerCase().includes(query)));
  if (query && !base.length) base = DATA.nodes.filter(n => JSON.stringify(n).toLowerCase().includes(query));
  const core = new Set(base.map(n => n.id)), nodeIds = new Set(core), edgeIds = new Set();
  for (const edge of edges.filter(e => !e.joint && (core.has(e.a) || core.has(e.b)))) {
    edgeIds.add(edge.id); nodeIds.add(edge.a); nodeIds.add(edge.b);
  }
  for (const j of DATA.joint_inferences) {
    if ((branch === 'all' && !query) || jointMembers(j).some(id => core.has(id))) {
      nodeIds.add(j.id); jointMembers(j).forEach(id => nodeIds.add(id));
      edges.filter(e => e.joint === j.id).forEach(e => edgeIds.add(e.id));
    }
  }
  return {nodeIds, edgeIds, coreIds:core};
}

function sourceMarkup(n) {
  if (!n.source) return '';
  const s = n.source;
  return `<h3>Source passage</h3><p>PDF page ${s.pdf_pages.join(', ')} · REPORT.md lines ${s.line_start}–${s.line_end}<br>${esc(s.section)}</p><details><summary>Read the source text</summary><pre class="source">${esc(s.passage)}</pre></details>`;
}
function jointMarkup(j) {
  return `<p>${esc(j.rule)}</p><h3>All premises are required</h3><p>${j.premises.map(ref).join(' ')}</p><h3>Supporting evidence</h3><p>${j.evidence.map(ref).join(' ')}</p><h3>Conclusions</h3><p>${j.conclusions.map(ref).join(' ')}</p>`;
}
function inspectNode(id) {
  const n = byId.get(id);
  let body = `<span class="tag">${esc(n.id)}</span><span class="tag">${esc(n.kind.replaceAll('_',' '))}</span>`;
  if (n.kind === 'joint_inference') {
    body += `<h2>Joint inference ${esc(n.id)}</h2>${jointMarkup(n)}`;
  } else {
    body += `<h2>${esc(n.title)}</h2><p>${esc(n.content)}</p><p><span class="tag">${esc(n.status)}</span><span class="tag">${esc(n.extraction_origin)}</span></p>`;
    if (n.answer_nodes) body += `<h3>Answer artifacts</h3><p>${n.answer_nodes.length ? n.answer_nodes.map(ref).join(' ') : 'Open in this document.'}</p>`;
    if (n.resolution_rule) body += `<h3>Resolution rule</h3><p>${esc(n.resolution_rule)}</p>`;
    if (n.interest) body += `<h3>Research status / interest</h3><p>${esc(n.interest.assessment.replaceAll('_',' '))}</p>${n.interest.reason ? `<p>${esc(n.interest.reason)}</p>` : ''}<p class="muted">${esc(n.interest.basis)}</p>`;
    if (n.contra_invariant_role) body += `<h3>Counter-condition and its target</h3><p>${esc(n.contra_invariant_role.target)}</p><p>${esc(n.contra_invariant_role.violated_condition)}</p><p><b>Result that remains valid:</b> ${esc(n.contra_invariant_role.preserved_result)}</p><p class="muted">${esc(n.contra_invariant_role.terminology)}</p>`;
    const joints = DATA.joint_inferences.filter(j => jointMembers(j).includes(id));
    if (joints.length) body += `<h3>Joint derivations</h3><p>${joints.map(j => ref(j.id)).join(' ')}</p>`;
    const related = edges.filter(e => !e.joint && (e.a === id || e.b === id));
    if (related.length) body += `<h3>Relations</h3><ul>${related.map(e => `<li>${ref(e.a)} <button class="ref relation-ref" data-edge-ref="${esc(e.id)}">${esc(e.label.replaceAll('_',' '))} →</button> ${ref(e.b)}<br><small class="muted">${esc(e.record.explanation)}</small></li>`).join('')}</ul>`;
    if (n.evidence_record) {
      const e = n.evidence_record;
      body += `<h3>Recorded evidence</h3><p>${esc(e.receipt)}<br>Recorded status: ${esc(e.recorded_status)}<br>Fresh proof replay: no</p><ul>${e.artifacts.map(a => `<li>${esc(a.path)}<br>Source binding: ${a.source_binding_matches ? 'matches' : 'DOES NOT MATCH'}<br>${esc(Object.keys(a.declarations).join(', '))}</li>`).join('')}</ul>`;
    }
    body += sourceMarkup(n);
  }
  $('inspector').innerHTML = body; $('inspector').scrollTop = 0; bindRefs();
}
function inspectEdge(edge) {
  let body = `<span class="tag">Relation</span><h2>${esc(edge.a)} → ${esc(edge.b)}</h2><p><b>${esc(edge.label.replaceAll('_',' '))}</b></p><p>${ref(edge.a)} ${ref(edge.b)}</p>`;
  if (edge.joint) body += jointMarkup(byId.get(edge.joint));
  else body += `<p>${esc(edge.record.explanation)}</p>`;
  body += '<p class="muted">The PDF highlights source passages of the connected objects. A reconstructed relationship is not necessarily a quoted sentence.</p>';
  $('inspector').innerHTML = body; $('inspector').scrollTop = 0; bindRefs();
}
function focusNode(id) {
  if (!byId.has(id)) return;
  selection = {type:'node', id}; render(); fit(); inspectNode(id);
  const n = byId.get(id);
  showSources(n.kind === 'joint_inference' ? [...n.conclusions, ...n.premises, ...n.evidence] : [id]);
  nodeElements.get(id)?.focus({preventScroll:true});
}
function focusEdge(id) {
  const e = edgeById.get(id); if (!e) return;
  selection = {type:'edge', id}; render(); fit(); inspectEdge(e);
  const j = e.joint && byId.get(e.joint);
  showSources(j ? [...j.conclusions, ...j.premises, ...j.evidence] : [e.b, e.a]);
  drawnEdges.find(edge => edge.id === id)?.group.focus({preventScroll:true});
}
function clearFocus() { selection = null; render(); fit(); }
function showBranchOverview() {
  clearFocus();
  const branch=DATA.four_principles.find(b=>b.id===$('branch').value);
  const title=branch?.title || 'Whole document', query=$('search').value.trim();
  const ids=[...branchScope().coreIds];
  let body=`<span class="tag">Branch overview</span><h2>${esc(title)}</h2>`;
  if(query) body+=`<p>Search: <b>${esc(query)}</b></p>`;
  body+=ids.length
    ? '<p>The PDF highlights source passages of the matching branch objects. Select an object or connection to inspect a specific passage.</p>'
    : '<p>No objects match this search. Clear the search to restore the branch.</p>';
  const questions=ids.filter(id=>byId.get(id).kind==='question');
  if(questions.length) body+=`<h3>Questions</h3><p>${questions.map(ref).join(' ')}</p>`;
  if(branch && ids.length) {
    for(const kind of ['assumptions','insights','justification']) {
      const members=branch[kind].filter(id=>ids.includes(id));
      if(members.length) body+=`<h3>${esc(kind[0].toUpperCase()+kind.slice(1))}</h3><p>${members.map(ref).join(' ')}</p>`;
    }
  }
  $('inspector').innerHTML=body; $('inspector').scrollTop=0; bindRefs();
  showSources(ids);
}
function resetPositions() {
  manualPositions={};
  try { localStorage.removeItem(layoutKey); } catch (_) {}
  render(); fit();
  $('selection-status').textContent+=' · Positions reset to automatic layout';
}
function toggleSelection(type, id) {
  if (selection?.type === type && selection.id === id) {
    clearFocus();
    const element=type === 'node' ? nodeElements.get(id) : drawnEdges.find(edge=>edge.id===id)?.group;
    element?.focus({preventScroll:true});
  } else if (type === 'node') focusNode(id);
  else focusEdge(id);
}

function svgElement(tag, attrs, parent) {
  const e = document.createElementNS('http://www.w3.org/2000/svg', tag);
  for (const [k, v] of Object.entries(attrs || {})) e.setAttribute(k, v);
  if (parent) parent.appendChild(e); return e;
}
function wrap(text, length = 29) {
  const lines = []; let line = '';
  for (const word of text.split(/\s+/)) {
    if ((line + ' ' + word).trim().length > length && line) { lines.push(line); line = word; }
    else line = (line + ' ' + word).trim();
  }
  if (line) lines.push(line);
  return lines.slice(0, 3).map((value, i) => i === 2 && lines.length > 3 ? value + '…' : value);
}
function overlaps(a, b) { return a.x < b.x+b.w+12 && a.x+a.w+12 > b.x && a.y < b.y+b.h+12 && a.y+a.h+12 > b.y; }
function arrange(nodes) {
  const columns = {goal:0,question:0,assumption:1,hypothesis:1,construction:1,counterexample:1,evidence:2,joint_inference:3,insight:4,invariant:4,limitation:5};
  const occupied = [], count = [0,0,0,0,0,0]; positions = new Map();
  const dimensions = n => ({w:n.kind === 'joint_inference' ? 110 : 220,h:96});
  for (const n of nodes) if (manualPositions[n.id]) {
    const p = {...manualPositions[n.id], ...dimensions(n)}; positions.set(n.id,p); occupied.push(p);
  }
  for (const n of nodes) if (!positions.has(n.id)) {
    const c = columns[n.kind]; let p;
    do { p = {x:24+c*260,y:58+count[c]++*120,...dimensions(n)}; } while (occupied.some(o => overlaps(p,o)));
    positions.set(n.id,p); occupied.push(p);
  }
  const points = [...positions.values()];
  viewX = points.length ? Math.max(0, Math.min(...points.map(p => p.x))-24) : 0;
  viewY = points.length ? Math.max(0, Math.min(...points.map(p => p.y))-40) : 0;
  viewWidth = Math.max(500, ...points.map(p => p.x+p.w+36-viewX));
  viewHeight = Math.max(360, ...points.map(p => p.y+p.h+36-viewY));
}
function edgeGeometry(edge) {
  const a = positions.get(edge.a), b = positions.get(edge.b);
  const right = b.x+b.w/2 >= a.x+a.w/2;
  const ax=a.x+(right?a.w:0), bx=b.x+(right?0:b.w), ay=a.y+a.h/2, by=b.y+b.h/2;
  const distance=Math.max(45,Math.abs(bx-ax)*.45);
  let d=`M ${ax} ${ay} C ${ax+(right?distance:-distance)} ${ay}, ${bx+(right?-distance:distance)} ${by}, ${bx} ${by}`;
  if (Math.abs(a.x-b.x)<10) d=`M ${a.x+a.w} ${ay} C ${a.x+a.w+80} ${ay}, ${b.x+b.w+80} ${by}, ${b.x+b.w} ${by}`;
  return {d,x:(ax+bx)/2,y:(ay+by)/2-7};
}
function updateEdges() {
  for (const edge of drawnEdges) {
    const geometry=edgeGeometry(edge);
    edge.path.setAttribute('d',geometry.d); edge.hit.setAttribute('d',geometry.d);
    edge.text.setAttribute('x',geometry.x); edge.text.setAttribute('y',geometry.y);
  }
}
function clientPoint(event) {
  const point=$('graph').createSVGPoint(); point.x=event.clientX; point.y=event.clientY;
  return point.matrixTransform($('graph').getScreenCTM().inverse());
}
function moveNode(id, x, y) {
  const p=positions.get(id); p.x=Math.max(12,x); p.y=Math.max(44,y);
  manualPositions[id]={x:p.x,y:p.y};
  nodeElements.get(id).setAttribute('transform',`translate(${p.x},${p.y})`);
  updateEdges();
}
function expandBounds() {
  const oldX=viewX, oldY=viewY;
  const points=[...positions.values()];
  viewX=Math.max(0,Math.min(viewX,...points.map(p=>p.x-12)));
  viewY=Math.max(0,Math.min(viewY,...points.map(p=>p.y-20)));
  viewWidth=Math.max(viewWidth,...points.map(p=>p.x+p.w+36-viewX));
  viewHeight=Math.max(viewHeight,...points.map(p=>p.y+p.h+36-viewY));
  zoom();
  $('canvas').scrollLeft+=(oldX-viewX)*scale;
  $('canvas').scrollTop+=(oldY-viewY)*scale;
}
function attachNodeControls(group, node) {
  group.addEventListener('pointerdown', event => {
    if (event.button !== 0 || (drag && drag.pointer !== event.pointerId)) return;
    const point=clientPoint(event), position=positions.get(node.id);
    drag={id:node.id,pointer:event.pointerId,startX:event.clientX,startY:event.clientY,
      dx:point.x-position.x,dy:point.y-position.y,moved:false};
    group.parentNode.appendChild(group);
    group.setPointerCapture(event.pointerId); event.preventDefault();
  });
  group.addEventListener('pointermove', event => {
    if (!drag || drag.id!==node.id || drag.pointer!==event.pointerId) return;
    if (!drag.moved && Math.hypot(event.clientX-drag.startX,event.clientY-drag.startY)<5) return;
    drag.moved=true; group.classList.add('dragging');
    const point=clientPoint(event); moveNode(node.id,point.x-drag.dx,point.y-drag.dy);
    event.preventDefault();
  });
  const finish = event => {
    if (!drag || drag.id!==node.id || drag.pointer!==event.pointerId) return;
    const moved=drag.moved; drag=null; group.classList.remove('dragging');
    if (group.hasPointerCapture(event.pointerId)) group.releasePointerCapture(event.pointerId);
    if (moved) { savePositions(); expandBounds(); }
    else if (event.type==='pointerup') toggleSelection('node',node.id);
  };
  group.addEventListener('pointerup',finish); group.addEventListener('pointercancel',finish);
  group.addEventListener('click',event=>{
    event.stopPropagation();
    if(event.detail===0) toggleSelection('node',node.id);
  });
  group.addEventListener('keydown', event => {
    if (event.key==='Enter'||event.key===' ') { event.preventDefault(); toggleSelection('node',node.id); }
    if (event.altKey && ['ArrowLeft','ArrowRight','ArrowUp','ArrowDown'].includes(event.key)) {
      event.preventDefault(); const p=positions.get(node.id), step=event.shiftKey?40:10;
      moveNode(node.id,p.x+(event.key==='ArrowRight'?step:event.key==='ArrowLeft'?-step:0),p.y+(event.key==='ArrowDown'?step:event.key==='ArrowUp'?-step:0));
      savePositions(); expandBounds();
    }
  });
}

function render() {
  const scope=selectedScope() || branchScope(); visibleNodes=scope.nodeIds;
  const nodes=[...scope.nodeIds].map(id=>byId.get(id)); arrange(nodes);
  const svg=$('graph'); svg.innerHTML=''; nodeElements=new Map(); drawnEdges=[];
  svg.dataset.selectionType=selection?.type || ''; svg.dataset.selectionId=selection?.id || '';
  const defs=svgElement('defs',{},svg);
  const marker=svgElement('marker',{id:'arrow',viewBox:'0 0 10 10',refX:9,refY:5,markerWidth:6,markerHeight:6,orient:'auto-start-reverse'},defs);
  svgElement('path',{d:'M 0 0 L 10 5 L 0 10 z',fill:'#47697d'},marker);
  for (const edge of edges.filter(e=>scope.edgeIds.has(e.id))) {
    const primary=selection?.type==='edge' && selection.id===edge.id;
    const group=svgElement('g',{class:'edge-group'+(primary?' selected-edge':''),tabindex:0,role:'button',
      'aria-label':`${edge.a} ${edge.label} ${edge.b}`,'aria-pressed':String(primary),'data-edge':edge.id},svg);
    const hit=svgElement('path',{class:'edge-hit'},group);
    const path=svgElement('path',{class:'edge '+edge.kind+(selection?' active':''),'marker-end':'url(#arrow)'},group);
    svgElement('title',{},group).textContent=`${edge.a} — ${edge.label} → ${edge.b}`;
    const text=svgElement('text',{class:'edge-label','text-anchor':'middle'},group);
    text.textContent=edge.label.replaceAll('_',' '); text.style.display=($('labels').checked||primary)?'':'none';
    group.onclick=event=>{event.stopPropagation();toggleSelection('edge',edge.id);};
    group.onkeydown=event=>{if(event.key==='Enter'||event.key===' '){event.preventDefault();toggleSelection('edge',edge.id);}};
    drawnEdges.push({...edge,group,path,hit,text});
  }
  for (const n of [...nodes].sort((a,b) => Number(selection?.id===a.id)-Number(selection?.id===b.id))) {
    const p=positions.get(n.id), primary=selection?.type==='node' && selection.id===n.id;
    const group=svgElement('g',{class:'node'+(primary?' selected-node':''),tabindex:0,role:'button',
      'aria-label':n.id+' '+(n.title||'Joint inference'),'aria-pressed':String(primary),
      'aria-describedby':'interaction-help',transform:`translate(${p.x},${p.y})`,'data-node':n.id},svg);
    const color=colors[n.kind];
    if(n.kind==='joint_inference') svgElement('polygon',{class:'node-shape',points:'55,0 110,48 55,96 0,48',fill:'#edf1f4',stroke:color},group);
    else {
      svgElement('rect',{class:'node-shape',width:p.w,height:p.h,rx:8,fill:primary?'#fff2d1':'#fff',stroke:color},group);
      svgElement('rect',{width:5,height:p.h-14,x:0,y:7,fill:color},group);
    }
    const x=n.kind==='joint_inference'?55:14, anchor=n.kind==='joint_inference'?'middle':'start';
    svgElement('text',{x,y:21,class:'node-id',fill:color,'text-anchor':anchor},group).textContent=n.id+(n.kind==='joint_inference'?' ALL':'');
    const lines=n.kind==='joint_inference'?['joint','premises']:wrap(n.title);
    lines.forEach((line,i)=>svgElement('text',{x,y:42+i*16,class:'node-label','text-anchor':anchor},group).textContent=line);
    svgElement('title',{},group).textContent=n.title||n.rule;
    nodeElements.set(n.id,group); attachNodeControls(group,n);
  }
  updateEdges(); zoom();
  const f=DATA.four_principles.find(f=>f.id===$('branch').value);
  $('principles').innerHTML=f?['question','assumptions','insights','justification'].map(k=>`<span><b>${esc(k.toUpperCase())}</b> ${f[k].map(ref).join(' ')||'See contextual dependencies'}</span>`).join(''):'<span>Select an object or a relation to isolate its connections.</span>';
  const name=selection?`${selection.type==='node'?'Object':'Relation'} ${selection.id}`:'Branch overview';
  $('selection-status').textContent=`${name} · ${nodes.length} objects · ${drawnEdges.length} connections${selection?' · other objects hidden':''}`;
  $('show-all').disabled=!selection; bindRefs();
}
function zoom() {
  $('graph').setAttribute('viewBox',`${viewX} ${viewY} ${viewWidth} ${viewHeight}`);
  $('graph').style.width=(viewWidth*scale)+'px'; $('graph').style.height=(viewHeight*scale)+'px';
}
function fit() {
  scale=Math.max(.3,Math.min(1.1,($('canvas').clientWidth-24)/viewWidth)); zoom();
  $('canvas').scrollTop=0; $('canvas').scrollLeft=0;
}

function showSources(ids) {
  ++pdfGeneration; // Invalidate an older image callback, including for an empty result.
  sourceIds=[...new Set(ids)].filter(id=>byId.get(id)?.source);
  sourcePages=[...new Set(sourceIds.flatMap(id=>byId.get(id).source.pdf_pages))].sort((a,b)=>a-b);
  $('pdf-panel').dataset.sourceIds=sourceIds.join(',');
  $('pdf-sources').textContent=sourceIds.length?'Source: '+sourceIds.join(', '):'No source selected';
  $('pdf-pages').innerHTML=sourcePages.map(page=>`<option value="${page}">Page ${page} / ${PDF_DATA.pages.length}</option>`).join('');
  if (!sourcePages.length) {
    $('pdf-scroll').textContent='No source page is recorded for this selection.';
    $('pdf-match').textContent='';
    $('pdf-prev').disabled=true; $('pdf-next').disabled=true;
    $('pdf-original').href='../NETWORK_REDUCTION.pdf';
    return;
  }
  const first=sourceIds[0], pages=byId.get(first).source.pdf_pages;
  pdfPage=pages.find(p=>(PDF_DATA.highlights[first]?.[String(p)]?.length ||
    PDF_DATA.equation_highlights?.[first]?.[String(p)]?.length)) || pages[0];
  renderPdf();
}
function renderPdf() {
  const generation=++pdfGeneration, page=PDF_DATA.pages.find(p=>p.number===pdfPage);
  $('pdf-pages').value=String(pdfPage);
  $('pdf-original').href=`../NETWORK_REDUCTION.pdf#page=${pdfPage}`;
  const index=sourcePages.indexOf(pdfPage);
  $('pdf-prev').disabled=index<=0; $('pdf-next').disabled=index>=sourcePages.length-1;
  const marks=[];
  for (const id of sourceIds) {
    for (const rect of PDF_DATA.highlights[id]?.[String(pdfPage)]||[]) marks.push({id,rect,kind:'text'});
    for (const rect of PDF_DATA.equation_highlights?.[id]?.[String(pdfPage)]||[]) marks.push({id,rect,kind:'equation'});
  }
  $('pdf-scroll').innerHTML=`<div class="pdf-sheet"><img id="pdf-image" src="${esc(page.image)}" alt="Source PDF page ${pdfPage}"><svg class="pdf-highlights" viewBox="0 0 ${page.width} ${page.height}" aria-label="Highlighted source passages">${marks.map(m=>`<rect data-source-node="${esc(m.id)}" data-source-kind="${m.kind}" x="${m.rect[0]}" y="${m.rect[1]}" width="${m.rect[2]-m.rect[0]}" height="${m.rect[3]-m.rect[1]}"/>`).join('')}</svg></div>`;
  const kind=marks.some(m=>m.kind==='equation')?'text and equations':'text';
  $('pdf-match').textContent=marks.length?`Matching source ${kind} is highlighted.`:'Source page shown; no exact text or equation match was found.';
  const position=()=>{
    if(generation!==pdfGeneration) return;
    const image=$('pdf-image'), top=marks.length?Math.min(...marks.map(m=>m.rect[1])):0;
    $('pdf-scroll').scrollTop=Math.max(0,top*(image.clientWidth/page.width)-45);
  };
  $('pdf-image').onload=position; if($('pdf-image').complete) position();
}

$('counts').textContent=`${DATA.nodes.length} objects · ${DATA.edges.length} typed relations · ${DATA.joint_inferences.length} joint inference records`;
$('branch').innerHTML='<option value="all">Whole document</option>'+DATA.four_principles.map(b=>`<option value="${b.id}">${esc(b.title)}</option>`).join('');
$('branch').value='all';
$('legend').innerHTML=Object.entries(colors).map(([k,v])=>`<span><b style="background:${v}"></b>${esc(k.replaceAll('_',' '))}</span>`).join('');
$('branch').onchange=showBranchOverview;
$('search').oninput=showBranchOverview;
$('labels').onchange=()=>{for(const e of drawnEdges) e.text.style.display=($('labels').checked||(selection?.type==='edge'&&selection.id===e.id))?'':'none';};
$('fit').onclick=fit;
$('plus').onclick=()=>{scale=Math.min(2.5,scale*1.25);zoom();};
$('minus').onclick=()=>{scale=Math.max(.2,scale/1.25);zoom();};
$('reset').onclick=()=>{$('search').value='';showBranchOverview();};
$('show-all').onclick=clearFocus;
$('reset-layout').onclick=resetPositions;
$('pdf-pages').onchange=()=>{pdfPage=Number($('pdf-pages').value);renderPdf();};
$('pdf-prev').onclick=()=>{const i=sourcePages.indexOf(pdfPage);if(i>0){pdfPage=sourcePages[i-1];renderPdf();}};
$('pdf-next').onclick=()=>{const i=sourcePages.indexOf(pdfPage);if(i<sourcePages.length-1){pdfPage=sourcePages[i+1];renderPdf();}};
document.addEventListener('keydown',event=>{if(event.key==='Escape'&&!drag){clearFocus();}});
// Redrawing on pointerup can retarget the subsequent click to the canvas.
// Only a gesture that actually started on its background may clear selection.
let backgroundPress=false;
$('canvas').addEventListener('pointerdown',event=>{
  backgroundPress=!event.target.closest('[data-node],[data-edge]');
},true);
$('canvas').addEventListener('click',event=>{
  if(backgroundPress && !drag && !event.target.closest('[data-node],[data-edge]')) clearFocus();
});
showBranchOverview();
