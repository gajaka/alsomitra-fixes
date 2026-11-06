"""Build the illustrated English guide without changing proof artifacts.

Requires ReportLab, markdown-it-py, Matplotlib, svglib, and the macOS
fonts registered by the shared document renderer. Display math is vector
artwork; the Markdown source retains ordinary $$ LaTeX equations.
"""
import argparse
from html import escape
import importlib.util
from io import BytesIO
import os
from pathlib import Path
import re
from urllib.parse import quote, urlsplit

HERE = Path(__file__).resolve().parent
os.environ.setdefault('MPLCONFIGDIR', str(HERE.parent / '.build/document-math-cache'))

from matplotlib import mathtext, rcParams, get_data_path
from matplotlib.font_manager import FontProperties
from markdown_it import MarkdownIt
from reportlab.graphics import renderPDF
from reportlab.lib.styles import ParagraphStyle
from reportlab.platypus import Flowable, PageBreak
from svglib.svglib import svg2rlg

spec = importlib.util.spec_from_file_location(
    'shared_document', HERE.parent / 'spec_compiler/docs/build_document.py')
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)
rcParams['mathtext.fontset'] = 'stix'
rcParams['svg.fonttype'] = 'path'
rcParams['savefig.transparent'] = True
r.pdfmetrics.registerFont(r.TTFont('MathSymbols',
    str(Path(get_data_path()) / 'fonts/ttf/STIXGeneral.ttf')))

BODY_SIZE = 10.3
r.styles['body'].fontSize = BODY_SIZE
r.styles['body'].leading = 14.4
r.styles['body'].spaceAfter = 8
r.styles['body'].allowWidows = 0
r.styles['body'].allowOrphans = 0
r.styles['title'].fontSize = 24
r.styles['title'].leading = 28
r.styles['h2'].fontSize = 15
r.styles['h2'].leading = 19
r.styles['h3'].spaceBefore = 10
r.styles['table'].fontSize = 9.1
r.styles['table'].leading = 12.3
r.styles['tablehead'].fontSize = 9.1
r.styles['tablehead'].leading = 12.3
r.styles['code'].fontSize = 8.7
r.styles['code'].leading = 11.5
FLOW_HEAD = ParagraphStyle('flowhead', parent=r.styles['body'],
    fontName='Body-Bold', fontSize=10, leading=13, spaceAfter=0)
FLOW_BODY = ParagraphStyle('flowbody', parent=r.styles['body'],
    fontSize=9.4, leading=12, spaceAfter=0)


def inline(children):
    # Use the body face for short mathematical tuples; use the monospace face
    # for source identifiers. Both remain actual searchable text in the PDF.
    out=[]
    for token in children or []:
        if token.type == 'link_open':
            href = token.attrGet('href')
            parsed = urlsplit(href)
            if not parsed.scheme and not href.startswith('#'):
                target = (HERE / parsed.path).resolve()
                relative = target.relative_to(HERE.parent.parent)
                if not target.exists():
                    raise ValueError('Missing document link target: ' + href)
                kind = 'tree' if target.is_dir() else 'blob'
                public = 'https://github.com/gajaka/alsomitra-fixes/' + kind + '/main/'
                public += quote(relative.as_posix())
                if parsed.fragment:
                    public += '#' + parsed.fragment
                token.attrSet('href', public)
        if token.type == 'code_inline':
            font = 'Mono' if re.fullmatch(r'[a-zA-Z0-9_./ -]+', token.content) else 'Body'
            size = '8.7' if font == 'Mono' else '10'
            out.append('<font name="'+font+'" size="'+size+'">'+escape(token.content)+'</font>')
        else:
            out.append(r.inline([token]))
    html = ''.join(out)
    # Arial/Courier on this machine lack Unicode subscript digits and two
    # arrows. Render subscripts typographically and use an embedded symbol
    # face for arrows, rather than emitting missing-glyph boxes.
    for old, new in zip('₀₁₂₃₄₅₆₇₈₉', '0123456789'):
        html = html.replace(old, '<sub>'+new+'</sub>')
    for symbol in ('⇒', '↦'):
        html = html.replace(symbol, '<font name="MathSymbols">'+symbol+'</font>')
    return html


class MathPanel(Flowable):
    def __init__(self, expression):
        super().__init__()
        self.expression = ' '.join(expression.strip().splitlines())
        svg = BytesIO()
        mathtext.math_to_image('$'+self.expression+'$', svg,
            prop=FontProperties(size=14), format='svg', color='#182b3b')
        svg.seek(0)
        self.drawing = svg2rlg(svg)
        scale = min(1, (r.WIDTH-24)/self.drawing.width)
        self.drawing.scale(scale, scale)
        self.drawing.width *= scale
        self.drawing.height *= scale
        self.width = r.WIDTH
        self.height = self.drawing.height + 20
        self.spaceBefore = 2
        self.spaceAfter = 10
        self.is_contract = self.expression.startswith(r'\forall x,y')

    def draw(self):
        c = self.canv
        c.setFillColor(r.LIGHT)
        c.setStrokeColor(r.TEAL)
        c.setLineWidth(1 if self.is_contract else .35)
        c.roundRect(0,0,self.width,self.height,4,stroke=1,fill=1)
        # Preserve an accessible description alongside the vector glyphs.
        actual = ('\ufeff'+self.expression).encode('utf-16-be').hex()
        c._code.append('/Span << /ActualText <'+actual+'> >> BDC')
        renderPDF.draw(self.drawing,c,(self.width-self.drawing.width)/2,10)
        c._code.append('EMC')


class FlowDiagram(Flowable):
    def __init__(self, content):
        super().__init__()
        self.rows=[]
        for line in content.strip().splitlines():
            title, detail = line.split('|',1)
            head=r.Paragraph(escape(title.strip()),FLOW_HEAD)
            body=r.Paragraph(escape(detail.strip()),FLOW_BODY)
            _,hh=head.wrap(r.WIDTH-56,1000)
            _,bh=body.wrap(r.WIDTH-56,1000)
            self.rows.append((head,body,hh,bh,hh+bh+16))
        self.width=r.WIDTH
        self.height=sum(row[-1] for row in self.rows)+12*(len(self.rows)-1)
        self.spaceBefore=3
        self.spaceAfter=10

    def draw(self):
        c=self.canv
        top=self.height
        for i,(head,body,hh,bh,height) in enumerate(self.rows):
            bottom=top-height
            c.setFillColor(r.LIGHT)
            c.setStrokeColor(r.colors.HexColor('#c5d9df'))
            c.roundRect(0,bottom,self.width,height,4,stroke=1,fill=1)
            c.setFillColor(r.TEAL)
            c.circle(18,bottom+height/2,10,fill=1,stroke=0)
            c.setFont('Body-Bold',10)
            c.setFillColor(r.colors.white)
            c.drawCentredString(18,bottom+height/2-3.4,str(i+1))
            head.drawOn(c,38,top-8-hh)
            body.drawOn(c,38,top-8-hh-bh)
            if i < len(self.rows)-1:
                c.setStrokeColor(r.TEAL)
                mid=self.width/2
                c.line(mid,bottom-1,mid,bottom-10)
                c.line(mid,bottom-10,mid-3,bottom-6)
                c.line(mid,bottom-10,mid+3,bottom-6)
            top=bottom-12


def source_tokens(source):
    # CommonMark has no display math token; recognize fenced $$ blocks first.
    lines=[]; in_math=False
    for line in source.splitlines():
        if line.strip()=='$$':
            lines.append('```' if in_math else '```math')
            in_math=not in_math
        else:
            lines.append(line)
    if in_math:
        raise ValueError('Unclosed display equation')
    return MarkdownIt('commonmark').enable('table').parse('\n'.join(lines))


def render(source, target):
    content=source.read_text()
    title=re.search(r'^# (.+)$',content,re.M).group(1)
    date=re.search(r'^Worked guide • revised (.+)$',content,re.M).group(1)
    tokens=source_tokens(content)
    story=[]; i=0; bullet=False
    while i<len(tokens):
        token=tokens[i]
        if token.type=='heading_open':
            heading=tokens[i+1]; level=int(token.tag[1])-1
            p=r.Paragraph(inline(heading.children),r.styles['title' if level==0 else 'h2' if level==1 else 'h3'])
            p.outline=(heading.content,level,'section-'+str(i))
            story.append(p);i+=3
        elif token.type=='paragraph_open':
            story.append(r.Paragraph(inline(tokens[i+1].children),r.styles['body'],bulletText='•' if bullet else None))
            bullet=False;i+=3
        elif token.type=='fence':
            kind=token.info.strip()
            if kind=='math':
                story.append(MathPanel(token.content))
            elif kind=='flow':
                story.append(FlowDiagram(token.content))
            else:
                for line in token.content.rstrip().splitlines():
                    if r.pdfmetrics.stringWidth(line,'Mono',8.7)>r.WIDTH-20:
                        raise ValueError('Code line too long: '+line)
                block=r.Table([[r.Preformatted(token.content.rstrip(),r.styles['code'])]],colWidths=[r.WIDTH],splitByRow=0)
                block.setStyle(r.TableStyle([
                    ('BACKGROUND',(0,0),(-1,-1),r.LIGHT),
                    ('LEFTPADDING',(0,0),(-1,-1),10),('RIGHTPADDING',(0,0),(-1,-1),10),
                    ('TOPPADDING',(0,0),(-1,-1),8),('BOTTOMPADDING',(0,0),(-1,-1),8)]))
                block.spaceAfter=10
                story.append(block)
            i+=1
        elif token.type=='table_open':
            rows=[];header=True;i+=1
            while tokens[i].type!='table_close':
                typ=tokens[i].type
                if typ=='tbody_open':header=False
                elif typ=='tr_open':row=[]
                elif typ=='inline':row.append(r.Paragraph(inline(tokens[i].children),r.styles['tablehead' if header else 'table']))
                elif typ=='tr_close':rows.append(row)
                i+=1
            i+=1
            n=len(rows[0]);ratios={2:[.39,.61],3:[.30,.30,.40],4:[.24,.27,.21,.28]}[n]
            table=r.Table(rows,colWidths=[r.WIDTH*x for x in ratios],repeatRows=1,hAlign='LEFT',splitByRow=0)
            table.setStyle(r.TableStyle([
                ('BACKGROUND',(0,0),(-1,0),r.TEAL),('VALIGN',(0,0),(-1,-1),'TOP'),
                ('ROWBACKGROUNDS',(0,1),(-1,-1),[r.colors.white,r.LIGHT]),
                ('LEFTPADDING',(0,0),(-1,-1),7),('RIGHTPADDING',(0,0),(-1,-1),7),
                ('TOPPADDING',(0,0),(-1,-1),5),('BOTTOMPADDING',(0,0),(-1,-1),5)]))
            table.spaceBefore=3;table.spaceAfter=10
            story.append(table)
        elif token.type=='html_block' and token.content.strip()=='<!-- pagebreak -->':
            story.append(PageBreak());i+=1
        elif token.type=='list_item_open':bullet=True;i+=1
        elif token.type in {'bullet_list_open','bullet_list_close','list_item_close'}:i+=1
        else:
            raise ValueError('Unsupported token '+token.type)

    def decoration(c,doc):
        c.setAuthor('');c.setCreator('')
        c.setSubject('Worked examples of robustness, certified reduction, RR and stable observable subalgebras')
        c.saveState();c.setFont('Body',8);c.setFillColor(r.MUTED)
        c.drawString(48,r.A4[1]-31,title)
        c.setStrokeColor(r.colors.HexColor('#d5dfe5'))
        c.line(48,r.A4[1]-38,r.A4[0]-48,r.A4[1]-38)
        c.line(48,37,r.A4[0]-48,37)
        c.drawString(48,24,'Worked guide  •  '+date)
        c.drawRightString(r.A4[0]-48,24,str(doc.page));c.restoreState()

    # ReportLab's frame adds 6 pt padding; these margins put the actual
    # content at 48 pt and make the usable width match the panels/tables.
    doc=r.GuidePDF(str(target),pagesize=r.A4,leftMargin=42,rightMargin=42,
        topMargin=55,bottomMargin=52,title=title,author='')
    doc.build(story,onFirstPage=decoration,onLaterPages=decoration)
    print(target)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,default=HERE/'REPORT.md')
    parser.add_argument('--output',type=Path,default=HERE/'NETWORK_REDUCTION.pdf')
    args=parser.parse_args()
    render(args.source,args.output)


if __name__=='__main__':
    main()
