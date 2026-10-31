from pathlib import Path
from reportlab.pdfgen import canvas
from reportlab.lib.pagesizes import A4,landscape
from reportlab.platypus import Paragraph,Table,TableStyle
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib.colors import HexColor
import json
H=Path(__file__).resolve().parent;O=Path.cwd()/'outputs/critical_family_continuation_20261031';O.mkdir(exist_ok=True)
pdfmetrics.registerFont(TTFont('Song','C:/Windows/Fonts/simsun.ttc',subfontIndex=0));body=ParagraphStyle('b',fontName='Song',fontSize=10.6,leading=17,spaceAfter=10,textColor=HexColor('#18334b'));small=ParagraphStyle('s',parent=body,fontSize=9,leading=14)
C=canvas.Canvas(str(O/'Q9_Critical_Family_and_Count_Exclusions.pdf'),pagesize=A4);C.setTitle('Q9 critical family and three certified count exclusions');C.setAuthor('Local research with independent certificate checks');page=0;Y=0;W=0;HH=0;title=''
def footer():
 C.setFont('Song',8.5);C.setFillColor(HexColor('#64748b'));C.drawString(45,24,'2026-10-31 | 本地研究快照；未上传；全局新上界未证明');C.drawRightString(W-45,24,str(page))
def new(t,wide=False):
 global page,Y,W,HH,title
 if page:footer();C.showPage()
 page+=1;W,HH=landscape(A4) if wide else A4;C.setPageSize((W,HH));title=t;Y=HH-49;C.setFillColor(HexColor('#123a5a'));C.setFont('Song',18);C.drawString(45,Y,t);Y-=27;C.setStrokeColor(HexColor('#dce8f2'));C.line(45,Y,W-45,Y);Y-=22
def p(t,style=body):
 global Y
 q=Paragraph(t,style);_,h=q.wrap(W-90,1000)
 if Y-h<55:new(title+'（续）')
 q.drawOn(C,45,Y-h);Y-=h+10
def eq(t):
 global Y
 if Y<95:new(title+'（续）')
 C.setFillColor(HexColor('#eef5fb'));C.roundRect(45,Y-29,W-90,34,5,fill=1,stroke=0);C.setFillColor(HexColor('#123a5a'));C.setFont('Courier',9.7);C.drawString(56,Y-16,t);Y-=43
new('Q9：临界家族压缩与三条计数排除')
p('<b>本轮结果。</b> 已取得并核对旧临界家族的 18,865 条转移，构造并独立复核 431 条方向禁历史，排除了六个原循环分量中的四个。随后得到三条带原始几何 CNF/RUP 证书的局部计数排除。全局上界没有收紧；项目报告的 235 是继承状态，本轮未重放该全局定理。')
p('三份新证书分别有 353、1264、284 步 RUP 推理。独立读取 DIMACS/LRAT、重建输入行并检查全部提示后均通过。它们不依赖 share 上限，也未进行新的 Lean 内核验证。')
p('<b>三个排除。</b> 下列方向字的不同数字代表互不相同的坐标。窗口顶点记为 x0 至 x9，alpha_i 是完整 snake 在 xi 的 singleton-square 数。各行所列条件不能同时成立；未列出的内部计数不受该行限制。')
eq('012310420: a3=3, a4<=5, a5<=3, a7<=5')
eq('012310450: a3<=5, a4<=3, a5<=4, a6<=4, a7=3')
eq('012342153: a4=3, a6<=3, a7<=5, a8<=5')
p('这里 a_i 仅在上面三行作为 alpha_i 的 ASCII 简写，不表示坐标。对任意不同实际坐标，平移及坐标置换保持 inducedness 与 singleton-square 数，因此结论适用于任意位置的匹配窗口。未声明理论首创。')
p('<b>模型影响。</b> 对明确保存的旧临界子图，经已有八条计数规则筛选后保留 18,737 条记录；三条新排除再删除 24 条。与 431 条方向规则合并后的显式乘积图仍有两个大循环分量和均值 480 的取等环，因此不能宣布 234。完整当前约 495 万转移图没有在本轮载入重算。')
new('1. 计数证书的完整解释链')
p('以第一行方向字为例，归一化后的窗口为 [0,1,3,7,15,13,12,28,24,25]。取八个内部中心的半径四球之并 B；布尔变量 Xv 表示完整路径在 B 内是否选择 v。窗口存在意味着整条路径至少九边，因而非平凡。')
p('<b>几何子句。</b> 所有窗口顶点被选中；任何选中顶点至多有两个选中邻点。若某顶点的九个邻点都在 B 内，则选中时至少有一个邻点。只对完整邻域建立 endpoint 见证，按完整路径中的选中度数一来解释；总数至多二。边界未知邻点从未被当成不存在。')
p('输入还禁止全部选中的四环及六环。它们在立方体中是实际的连通二正则子图，不能包含在一个 induced path 中。独立程序重建源子句，并对证书保留的环子句检查实际立方体邻接。')
p('<b>计数子句。</b> 每个内部窗口中心已经有两个选中邻点，故剩余七个单位邻点都不选中。singleton square 因此对应这七个坐标两两组合中的缺失对角点，共 21 个候选。alpha 的上、下界转成这些对角点布尔值的 at-most 约束。')
p('<b>辅助计数器扩展。</b> 对任一 at-most-k 顺序计数器，把 s[i,j] 解释为前 i+1 个输入中至少 j+1 个为真。若约束成立，此赋值满足每条计数器蕴含及溢出子句。不同组分配不同变量。对没有保留的计数假设，不要求满足被丢弃的末端约束。')
p('<b>核心支持与逻辑矛盾。</b> 第一份核心仅保留 alpha3 的上、下界 3，alpha4 的上界 5，alpha5 的上界 3，alpha7 的上界 5；第二、三份按各自清单核对。假如真实 snake 满足相应条件，它的选择变量及上述辅助扩展将满足核心全部子句。')
p('每条 RUP 推理在假设拟添加子句为假后，按提示逐步进行单元传播，最终产生冲突，所以新子句是原子句的逻辑后果。三份序列分别归纳到空子句，与满足赋值矛盾。原行索引、变量重命名、全部子句和全部提示都在独立证书目录中。')
new('2. 一条计数排除的几何窗口',True)
C.drawImage(str(H/'figures/count_window_exclusion.png'),45,90,width=W-90,height=(W-90)*750/1320,preserveAspectRatio=True,mask='auto');C.setFont('Song',10);C.setFillColor(HexColor('#334155'));C.drawString(45,64,'该方向窗口本身是合法诱导路径；矛盾来自四个高亮计数条件与完整 snake 几何的同时成立。')
new('3. 从精确转移 ID 提升到方向禁形')
p('先按冻结势函数的 SHA256 解码 1,601,856 个整数势值，并逐条核验 18,865 条记录满足 w+pi(u)-pi(v)=480。这里只独立核对已下载记录的紧性，没有借此宣称复验原提取程序的完整性或全部 495 万条边。')
p('旧冻结图使用六条已完成规则；当前八条规则比它多 7203 与 7216。独立匹配每个相应子窗口与全部计数区间，命中数为 116、34，交集 22，净删 128 条。数字 6 的语义是整个区间 [6,21]，并非精确六。筛选没有利用区间内部未证明的上界。')
p('一开始得到 222 个精确 ID 禁历史，但 ID 还带计数、share 历史。一个幸存环通过改用不同计数记录逃过匹配，方向模式却已被证明不可能。因此应把禁历史投影到九方向字的序列；它与具体计数无关。投影得 111 个不同方向历史，删除包含较短禁子串的冗余项后，等价基为 63 个。')
p('再对投影方向图的全部三符号路径 1181 个、没有坏三元子串的五符号路径 15184 个做精确几何检查。得到 44 个三元、358 个五元禁历史，与此前逐轮发现的规则合并为 431 个最小方向模式。独立程序不用 fresh-coordinate 对称合并或状态去重，尝试所有九坐标分支，复核全部 431 个模式均不可能。')
p('<b>压缩方法。</b> AC 自动机负责匹配禁子串。精确 ID 前缀能确定原图终点；方向前缀不能确定计数状态，因此方向版本必须使用可达的 (原状态, AC状态) 稀疏乘积。不能继续使用“一前缀只配一个原顶点”的 ID 特化。')
p('完整保存的 431 模式乘积有 96,350 个状态、317,570 条边。独立检查覆盖每条允许边、每个禁止 outgoing、所有 failure/bad 后缀和从空历史种子的可达性。两个循环分量仍存。其每条边对拉回势函数都恰紧，且有 17 边总重 8160 的环，所以该显式子图的最小环均值严格等于 480。')
new('4. 桶余量、share 探测与依赖修正')
p('项目已有定理：在不同坐标的方向字 (a,b,c,d,e,a) 中，alpha1+alpha4+alpha5 至少 13。若截断记录是 (3,3,6)，第三个实际计数至少 7，不能只记作六。正缺口只能落在唯一的 ≥6 桶上，因为两个这样的桶加一个至少一的计数已经不小于 13。')
p('对同一真实计数的多条要求必须取最大，不可相加。这样加强了 1096 条旧临界记录。固定位置平均可形成安全的额外权重，但端点预算仍需另行核验。即使与 431 条方向规则及三条新计数排除合并，仍保存了全部计数小于六、均值 480 的环；该环对这些桶余量机制没有收益。')
p('<b>share 简化。</b> 若 q 邻接一个已选中的收费中心，则 1≤d(q)≤9，所以 floor(12 E(q)/d(q)) 为零当且仅当空方形数 E(q) 为零。零 share 可用相应方形必须非空的正子句表达，不需要商计数器。这给出快速的局部探测。')
p('随后引入空面加权计数的安全下界作辅助搜索，在 cap15、31、63 下取得相同矛盾依赖。向后审计发现，三份被保留的最终矛盾只依赖原几何与计数输入，不使用 share cap、空面定义或 PB 约束。把它们解释为非平凡的 share 下界会掩盖更强的普通计数排除。')
p('因此此前对相同精确前提写出的 share 至少 16、32、64 是不可能前提的推论，不作为独立 share 改进计数。已剥离全部无关输入，分别形成 1052、1617、1137 条原始核心子句，以及 353、1264、284 步独立可验 RUP。一个冷启动 base 搜索十秒返回 UNKNOWN，不影响这份另行发现并重放通过的证明。')
new('5. 实际进度、精确门槛与复现',True)
C.drawImage(str(H/'figures/critical_family_progress.png'),45,HH-435,width=W-90,height=(W-90)*600/1300,preserveAspectRatio=True,mask='auto');Y=HH-465
p('若沿用项目的条件边数公式，改进到 234 仍需 227p &gt; 111960d+R。对 d=1、R=578，即均值必须严格超过 112538/227；整数 496 在 R≤631 时足够。当前仍有均值 480 取等环，因此没有达到这个条件。',small)
p('复现：verify_frozen_data.py；filter_current_cases.py；review_short_closure.py；export_count_exclusions.py；verify_count_exclusions.py；apply_count_rules.py。所有状态和输入 SHA、完整 CNF/LRAT 及制图程序均留在交付 ZIP。未上传仓库，也未进行新 Lean 内核回放。',small)
footer();C.save();print(O/'Q9_Critical_Family_and_Count_Exclusions.pdf')
