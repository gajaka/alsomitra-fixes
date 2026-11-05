"""Render the English reference-checker guide as a local PDF.

Requires reportlab and markdown-it-py. This renderer does not participate in
the compiler's proof chain or change its checked source/artifacts.
"""
import argparse
from html import escape
from pathlib import Path
import re

from markdown_it import MarkdownIt
from reportlab.lib import colors
from reportlab.lib.enums import TA_LEFT
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,Table,TableStyle,Preformatted

HERE=Path(__file__).resolve().parent
FONTDIR=Path('/System/Library/Fonts/Supplemental')
for name,file in (('Body','Arial.ttf'),('Body-Bold','Arial Bold.ttf'),
                  ('Body-Italic','Arial Italic.ttf'),('Body-BoldItalic','Arial Bold Italic.ttf'),
                  ('Mono','Courier New.ttf')):
    pdfmetrics.registerFont(TTFont(name,str(FONTDIR/file)))
pdfmetrics.registerFontFamily('Body',normal='Body',bold='Body-Bold',italic='Body-Italic',boldItalic='Body-BoldItalic')

INK=colors.HexColor('#182b3b')
TEAL=colors.HexColor('#126675')
LIGHT=colors.HexColor('#eef3f6')
MUTED=colors.HexColor('#516370')
WIDTH=A4[0]-96
styles={
 'body':ParagraphStyle('body',fontName='Body',fontSize=10,leading=14,textColor=INK,spaceAfter=7),
 'title':ParagraphStyle('title',fontName='Body-Bold',fontSize=25,leading=30,textColor=INK,spaceAfter=14,keepWithNext=True),
 'h2':ParagraphStyle('h2',fontName='Body-Bold',fontSize=14,leading=18,textColor=TEAL,spaceBefore=16,spaceAfter=8,keepWithNext=True),
 'h3':ParagraphStyle('h3',fontName='Body-Bold',fontSize=11,leading=15,textColor=INK,spaceBefore=10,spaceAfter=6,keepWithNext=True),
 'table':ParagraphStyle('table',fontName='Body',fontSize=8.6,leading=12,textColor=INK,splitLongWords=True),
 'tablehead':ParagraphStyle('tablehead',fontName='Body-Bold',fontSize=8.6,leading=12,textColor=colors.white),
 'code':ParagraphStyle('code',fontName='Mono',fontSize=9,leading=12,textColor=INK,alignment=TA_LEFT),
}


def inline(children):
    out=[]
    for c in children or []:
        if c.type=='text':out.append(escape(c.content))
        elif c.type=='code_inline':out.append('<font name="Mono" size="8.7">'+escape(c.content)+'</font>')
        elif c.type=='strong_open':out.append('<b>')
        elif c.type=='strong_close':out.append('</b>')
        elif c.type=='em_open':out.append('<i>')
        elif c.type=='em_close':out.append('</i>')
        elif c.type=='link_open':out.append('<a color="#126675" href="'+escape(c.attrGet('href'),quote=True)+'">')
        elif c.type=='link_close':out.append('</a>')
        elif c.type=='hardbreak':out.append('<br/>')
        elif c.type=='softbreak':out.append(' ')
        else:raise ValueError('Unsupported inline token '+c.type)
    return ''.join(out)


class GuidePDF(SimpleDocTemplate):
    def afterFlowable(self,flowable):
        if hasattr(flowable,'outline'):
            title,level,key=flowable.outline
            self.canv.bookmarkPage(key)
            self.canv.addOutlineEntry(title,key,level=level,closed=False)


def decoration(c,doc):
    c.setAuthor('')
    c.setCreator('')
    c.saveState()
    c.setFont('Body',8)
    c.setFillColor(MUTED)
    c.drawString(48,A4[1]-31,doc.title)
    c.setStrokeColor(colors.HexColor('#d5dfe5'))
    c.line(48,A4[1]-38,A4[0]-48,A4[1]-38)
    c.line(48,37,A4[0]-48,37)
    c.drawString(48,24,'Formal contract and executable example  •  5 November 2026')
    c.drawRightString(A4[0]-48,24,str(doc.page))
    c.restoreState()


def render(source=HERE/'REFERENCE_CHECKER.md', target=HERE/'REFERENCE_CHECKER.pdf',
           title='A Reference Checker for Input Specifications'):
    tokens=MarkdownIt('commonmark').enable('table').parse(source.read_text())
    story=[];i=0;bullet=False
    while i<len(tokens):
        t=tokens[i]
        if t.type=='heading_open':
            heading=tokens[i+1];level=int(t.tag[1])-1
            p=Paragraph(inline(heading.children),styles['title' if level==0 else 'h2' if level==1 else 'h3'])
            p.outline=(heading.content,level,'section-'+str(i))
            story.append(p);i+=3
        elif t.type=='paragraph_open':
            p=Paragraph(inline(tokens[i+1].children),styles['body'],bulletText='•' if bullet else None)
            story.append(p);bullet=False;i+=3
        elif t.type=='fence':
            for line in t.content.rstrip().splitlines():
                if pdfmetrics.stringWidth(line,'Mono',9)>WIDTH-20:
                    raise ValueError('Code line too long: '+line)
            block=Table([[Preformatted(t.content.rstrip(),styles['code'])]],colWidths=[WIDTH])
            block.setStyle(TableStyle([
                ('BACKGROUND',(0,0),(-1,-1),LIGHT),('LEFTPADDING',(0,0),(-1,-1),10),
                ('RIGHTPADDING',(0,0),(-1,-1),10),('TOPPADDING',(0,0),(-1,-1),8),
                ('BOTTOMPADDING',(0,0),(-1,-1),8)]))
            story.extend([Spacer(1,3),block,Spacer(1,10)]);i+=1
        elif t.type=='table_open':
            rows=[];row=[];header=True;i+=1
            while tokens[i].type!='table_close':
                typ=tokens[i].type
                if typ=='tbody_open':header=False
                elif typ=='tr_open':row=[]
                elif typ=='inline':row.append(Paragraph(inline(tokens[i].children),styles['tablehead' if header else 'table']))
                elif typ=='tr_close':rows.append(row)
                i+=1
            i+=1
            n=len(rows[0]);ratios={2:[.40,.60],3:[.25,.37,.38],4:[.26,.21,.18,.35],5:[.20]*5}[n]
            tab=Table(rows,colWidths=[WIDTH*r for r in ratios],repeatRows=1,hAlign='LEFT')
            tab.setStyle(TableStyle([
                ('BACKGROUND',(0,0),(-1,0),TEAL),('VALIGN',(0,0),(-1,-1),'TOP'),
                ('ROWBACKGROUNDS',(0,1),(-1,-1),[colors.white,LIGHT]),
                ('LEFTPADDING',(0,0),(-1,-1),7),('RIGHTPADDING',(0,0),(-1,-1),7),
                ('TOPPADDING',(0,0),(-1,-1),5),('BOTTOMPADDING',(0,0),(-1,-1),5),
                ('LINEBELOW',(0,0),(-1,0),.5,TEAL)]))
            story.extend([Spacer(1,4),tab,Spacer(1,12)])
        elif t.type=='list_item_open':bullet=True;i+=1
        elif t.type in {'bullet_list_open','bullet_list_close','list_item_close'}:i+=1
        else:raise ValueError('Unsupported token '+t.type)
    doc=GuidePDF(str(target),pagesize=A4,leftMargin=48,rightMargin=48,topMargin=55,bottomMargin=52,
        title=title,author='',
        subject='Formal contract, Lean implementation, and worked example')
    doc.build(story,onFirstPage=decoration,onLaterPages=decoration)
    print(target)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,default=HERE/'REFERENCE_CHECKER.md')
    parser.add_argument('--output',type=Path,default=HERE/'REFERENCE_CHECKER.pdf')
    parser.add_argument('--title',default='A Reference Checker for Input Specifications')
    args=parser.parse_args()
    render(args.source,args.output,args.title)
