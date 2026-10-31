from pathlib import Path
import json,sys
from reportlab.platypus import SimpleDocTemplate,Paragraph,PageBreak,Spacer,Table,TableStyle,Flowable
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.colors import HexColor
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
R=Path(__file__).resolve().parent; O=Path(sys.argv[1]) if len(sys.argv)>1 else R/'rendered';O.mkdir(parents=True,exist_ok=True)
if Path('C:/Windows/Fonts/simsun.ttc').exists():pdfmetrics.registerFont(TTFont('Song','C:/Windows/Fonts/simsun.ttc',subfontIndex=0));FONT='Song'
else:
 from reportlab.pdfbase.cidfonts import UnicodeCIDFont
 pdfmetrics.registerFont(UnicodeCIDFont('STSong-Light'));FONT='STSong-Light'
b=ParagraphStyle('b',fontName=FONT,fontSize=10.5,leading=16.8,spaceAfter=10,textColor=HexColor('#18334b'))
h=ParagraphStyle('h',parent=b,fontSize=20,leading=28,spaceAfter=20,textColor=HexColor('#12546a'))
f=ParagraphStyle('f',parent=b,fontSize=11,leading=18,leftIndent=10,backColor=HexColor('#eaf4f6'),borderPadding=8,spaceBefore=5,spaceAfter=14)
small=ParagraphStyle('s',parent=b,fontSize=8.8,leading=13)
S=[]
def p(x,style=b):S.append(Paragraph(x,style))
def title(x):p(x,h)
def eq(x):p(x,f)
def page():S.append(PageBreak())
def table(rows):
 t=Table([[Paragraph(str(c),small) for c in r] for r in rows],colWidths=[140,160,175]);t.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'TOP'),('GRID',(0,0),(-1,-1),.4,HexColor('#bfd4dc')),('BACKGROUND',(0,0),(-1,0),HexColor('#dceef2')),('TOPPADDING',(0,0),(-1,-1),7),('BOTTOMPADDING',(0,0),(-1,-1),7)]));S.append(t);S.append(Spacer(1,12))
val=json.loads((R/'validation.json').read_text());summary=json.loads((R/'cheap_summary.json').read_text())
class Benchmark(Flowable):
 def __init__(self):self.width=460;self.height=115
 def draw(self):
  c=self.canv;c.setFont(FONT,9)
  for j,(lab,ratio) in enumerate([('完整收费扫描',val['census_speedup']),('相同前缀序列',val['prefix_scan_speedup'])]):
   y=85-j*48;c.setFillColor(HexColor('#18334b'));c.drawString(0,y+8,lab);c.setFillColor(HexColor('#147f95'));c.rect(110,y,ratio*19,15,fill=1,stroke=0);c.setFillColor(HexColor('#18334b'));c.drawString(115+ratio*19,y+3,f'{ratio:.2f}x')
title('Q9：沿项目窗口管线继续推进')
p('代码优化与严格局部计数补充 · 2026-10-29',f)
p('本轮沿 GitHub 的 share / w3、固定路径窗口、CNF 阈值和可重放证书路线推进。没有使用 Ramsey 方法，也没有证明新的无条件数值上界。已完成新的局部不等式、整数编码优化、真实数据扫描及完整几何编码的正对照。')
table([['项目','完成结果','证明状态'],['精确收费引擎','位集缓存、1260/21 整数缩放、蛇尾增量更新','与旧有理数实现精确一致'],['新低系数目标','21α+2e2+e3+V','普通数学证明完成；尚未 Lean 形式化'],['CNF 原型','固定路径常量折叠；二进制加法与比较','正负对照通过；无自由窗口 UNSAT 结论'],['样本扫描','131 条已知蛇；1703 个长前缀；208/224 环并集','仅为样本结果，不能作为通用下界']])
S.append(Benchmark())
p('计时为本机七次或三次重复的中位数，不含几何预计算。原始秒数、随机种子、命令及对照结果随代码包交付。性能结果会随机器变化。',small)
page();title('1  新的低系数窗口目标：完整证明')
p('设 S⊆Q9 不含完整方形，x∈S。α(x) 为以 x 为唯一所选点的方形数。e2(x)、e3(x) 分别是距 x 恰为 1 的空方形、空三维立方体数。对这样的空方形 F，h(F) 是其七个三维母立方体中非空者的数目；R_x(F) 是唯一包含 x 的母立方体，t=|R_x(F)∩S|。')
eq('a(x) = α(x) + Σ_{F 空，dist(x,F)=1} 2/[h(F)t_x(F)].')
p('因为 F 为空，R_x(F) 内所选点都在对面方形中；无完整方形保证 1≤t≤3，同时 1≤h≤7。这给出精确整数缩放：1260a(x) 的每项为 2520/(ht)，均为整数。均匀收费 g 的 21 倍也为整数。')
p('引理。令 D(x)=Σ_F(7-h(F))，则 D(x)=3e3(x)。证明：左侧数对 (F,R)，其中 R 是 F 的空母立方体。R 距 x 为 1，且有唯一最近点 y；R 的六个面中恰有三个包含 y，这三个面恰是距 x 为 1 的面。反向也成立，故每个空 R 被数三次。')
p('对 h∈{1,...,7}，(h-6)(h-7)≥0，所以 2/(3h)≥(13-h)/63。再用 t≤3，逐个 F 相加：')
eq('a(x) ≥ α(x) + [6e2(x)+D(x)]/63<br/>= α(x) + [2e2(x)+e3(x)]/21.')
p('更一般地，对整数 r=1,...,6，用 (h-r)(h-r-1)≥0 得到：')
eq('a(x) ≥ α(x) + 4(r-3)e2(x)/[3r(r+1)]<br/>+ 2e3(x)/[r(r+1)].')
p('r=3,4,5,6 分别给出正整数目标 6α+e3、30α+2e2+3e3、45α+4e2+3e3、21α+2e2+e3，缩放依次为 6、30、45、21。它们需要半径 4；不能把半径外未知点当成未选中。')
page();title('2  单点／两点三维立方体的严格加强')
p('定义 C1(x) 为含 x 且恰有一个所选点的三维立方体数。C2,d(x) 为含 x 且恰有两个所选点、两点距离为 d 的三维立方体数。令 V(x)=12C1(x)+2C2,1(x)+C2,2(x)。')
p('对距 x 为 1 的空 F，记 E1 为 t=1 的个数、E≤2 为 t≤2 的个数。一个单点三维立方体给出三个这样的空面；两点距离 d 时，恰有 3-d 个坐标在两点上相同，故恰给出 3-d 个空对面。于是 E1=3C1，E≤2=3C1+2C2,1+C2,2，距离 3 的两点情形贡献为零。')
p('精确恒等式 1/t=(2+[t≤2]+3[t=1])/6 与上一页的 h 支撑线相乘。分出前导 2 项后，其余项用 13-h≥6 下界：')
eq('2/(ht) ≥ (13-h)/63 + ([t≤2]+3[t=1])/21.<br/>21a(x) ≥ 21α(x)+2e2(x)+e3(x)+V(x).')
p('因为 E≤2+3E1=V，求和即得第二行。r=4、5 同样可加入 V、2V，分别得到 30α+2e2+3e3+V 和 45α+4e2+3e3+2V。这些加强都只用正系数。')
p('全局推论。对非平凡蛇，设 v=|S|、T=Σα、B2=Σe2、B3=Σe3，N1、N2,d 分别数整个 Q9 中单点、两点距离 d 的三维立方体。由精确收费 Σa+2U=T+2E2=9214-35v，U≥0，以及 ΣV=12N1+4N2,1+2N2,2，有')
eq('21T + 2B2 + B3 + 12N1 + 4N2,1 + 2N2,2<br/>≤ 21(9214 - 35v).')
p('这是严格成立的新计数关系。它本身还没有给出所需的通用窗口均值下界，不能把样本最小值代入来宣称更紧的 a(9) 上界。相关母纤维分布、259 个实际蛇根、全部标量系数和距离 3 特例均已验证。')
page();title('3  沿用原 Encoding 的实现与对照')
p('精确引擎。用 Python 大整数位集缓存方形、三维立方体和关联关系；以整数代替 Fraction。删除蛇尾时，仅更新包含被删点的方形及其平移对面，不重算全图。193 个无方形 Q3 子集、300 个随机 Q4 集合和 Q9 样本与旧实现一致；17 次蛇尾删除的所有逐点分数与全量重算一致。')
p('常量折叠。窗口内点的两个相邻路径点固定选中，其他七个邻居必须未选中。因此 α 的 36 个方形测试可约化为 21 个对角点的否定文字。空集门先代入固定真／假值，再共享同一几何集合的门；所有这些固定值都写入单位子句。恒真项保存为 offset，阈值必须减去 offset。')
table([['九中心原型','变量数','子句数（不含 PB／几何）'],['未折叠目标','4428','28524'],['固定路径折叠','3026','15794'],['加强目标，二进制门共享','4084','20992']])
p('阈值编码。加权项经二进制展开后，用 carry-save 全加器压缩，再用进位加法器及逐位比较器表达 ≤cap。每个门都是双向等价子句，不允许只声明单向目标标记。820 个完整标量赋值通过真值表测试；256 个随机局部赋值验证了折叠前后等价。')
p('直接重用 GitHub wincert.py 的 Encoding 类，保留其原始 build/atmost 方法；只跳过不使用的求解器导入。原文件 SHA256 随查询记录保存。加强目标九中心完整正对照有 19,325 个变量、160,459 条子句，已知 bank67 蛇给出满足全部子句的赋值。固定全部 bank 输入后，精确阈值通过、阈值减 1 被单位传播驳回。')
p('自由查询已输出：同一窗口的加强目标 cap=850，19,321 变量、160,447 子句。单位传播未驳回。尚无 SAT 求解结果、LRAT 证书或 Lean 目标语义证明；850 是探索阈值，不是已证明下界。',f)
page();title('4  扫描结果、复现与验收边界')
p('已知蛇扫描。131 条 191 边蛇的 180...192 顶点前缀共 1703 个集合已扫描，支持记录进度并恢复。所有完整蛇的 U=0；长前缀中 280 个集合出现 U>0，最长仍为 183 边。该结果不证明更长蛇都满足 U=0。')
rows=[['中心数／样本最小均值','基础低系数目标','加入 V 后']]
for k in (3,5,7,9):
 old=summary['objectives']['r6'][str(k)]['mean_display'];new=summary['objectives']['r6plus'][str(k)]['mean_display'];rows.append([f'{k} 个中心',f'{old:.6f}',f'{new:.6f}'])
table(rows)
p('上表所有数值都只是已知蛇样本的最小值。环并集对照中，208 顶点／八个 26 环的加强目标均值约为 9.132；224 顶点／十六个 14 环约为 6.034。它们不是蛇，不能代替连通性证明。保留这些对照是为了避免新目标只拟合已有长蛇。')
p('代码包目录保留 branch241-next 与 branch241-audit 两个相邻目录；后者仅含复现所需的原始参考文件，不是完整 Lean checkout。在 branch241-next 中可运行下列命令：',b)
for cmd in ['python validate_fast.py','python scan_bank.py','python scan_cheap.py','python local_coefficients.py','python coefficient_identities.py','python bonus_validation.py','python encoding/validate_folded.py','python encoding/build_pb_controls.py','python encoding/github_query.py']:p(cmd,small)
p('验收顺序。先用项目可用的 CaDiCaL 环境解自由窗口模型；SAT 时按项目逻辑加入额外环的有效排除约束。若得到 UNSAT，冷启动重建实际 CNF 并导出、检查证明；随后完成新增计数门、PB 门与全局不等式的 Lean 语义桥接，再进入全状态加权自动机核验。普通 SAT 模型若仍有边界片段，不能称为全局真蛇。')
p('本机缺少可用的 CaDiCaL／Lean 运行时；没有安装或尝试绕过被系统阻止的原生库。已经完成可独立验证的数学与编码工作，并留下可直接送入项目求解环境的静态查询。本轮没有更新 235 的历史审计状态，也没有把 234 候选提升为已认证结论。',small)
def footer(c,d):
 c.setStrokeColor(HexColor('#c8dce2'));c.line(50,43,545,43);c.setFont(FONT,8);c.drawString(50,30,'Q9 · GitHub window / share pipeline · 2026-10-29');c.drawRightString(545,30,str(d.page))
SimpleDocTemplate(str(O/'Q9_Window_Optimization_Progress.pdf'),pagesize=(595.28,841.89),leftMargin=60,rightMargin=60,topMargin=48,bottomMargin=58).build(S,onFirstPage=footer,onLaterPages=footer)
print(O/'Q9_Window_Optimization_Progress.pdf')
