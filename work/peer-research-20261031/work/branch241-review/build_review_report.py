"""Reproducible report and vector figures; stdlib+ReportLab only."""
from pathlib import Path
import sys,json,math,gzip
from xml.sax.saxutils import escape
from reportlab.pdfgen import canvas
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,Flowable
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.colors import HexColor
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
R=Path(__file__).resolve().parent;ROOT=R.parents[1];OUT=ROOT/'outputs/branch241_peer_review_20261030';OUT.mkdir(parents=True,exist_ok=True)
pdfmetrics.registerFont(TTFont('Chinese','C:/Windows/Fonts/simsun.ttc',subfontIndex=0))
styles={
 'title':ParagraphStyle('title',fontName='Chinese',fontSize=24,leading=33,textColor=HexColor('#15354b'),spaceAfter=20),
 'h':ParagraphStyle('h',fontName='Chinese',fontSize=17,leading=24,textColor=HexColor('#15354b'),spaceAfter=14),
 'body':ParagraphStyle('body',fontName='Chinese',fontSize=11,leading=18,spaceAfter=10),
 'eq':ParagraphStyle('eq',fontName='Chinese',fontSize=11,leading=18,leftIndent=14,backColor=HexColor('#edf4f7'),borderPadding=7,spaceBefore=5,spaceAfter=14),
 'small':ParagraphStyle('small',fontName='Chinese',fontSize=9,leading=14,spaceAfter=7)}
story=[]
def p(t,k='body'):story.append(Paragraph(escape(t).replace('\n','<br/>'),styles[k]))
def page(t):
 if story:story.append(PageBreak())
 p(t,'h')
class CycleFigure(Flowable):
 def __init__(self):super().__init__();self.width=450;self.height=180
 def draw(self):
  C=self.canv;coords=[(95+65*math.cos(2*math.pi*i/8),85+65*math.sin(2*math.pi*i/8)) for i in range(8)]
  # Genuine induced Q4 C8: each transition direction twice, no chords.
  vs=[0,1,3,7,15,14,12,8]
  assert all(((vs[i]^vs[j]).bit_count()==1)==(abs(i-j)==1 or abs(i-j)==7) for i in range(8) for j in range(i))
  C.setStrokeColor(HexColor('#c2573c'));C.setLineWidth(2)
  for i in range(8):C.line(*coords[i],*coords[(i+1)%8])
  C.setFont('Chinese',9)
  for i,(x,y) in enumerate(coords):
   C.setFillColor(HexColor('#15354b'));C.circle(x,y,4,fill=1);C.drawString(x-10,y+10,format(vs[i],'04b'))
  C.setFillColor(HexColor('#15354b'));C.setFont('Chinese',11)
  for j,s in enumerate(['一个真正的诱导八环','每条边翻转一位；非相邻点不邻接。','局部 degree≤2、禁四环和六环','仍允许这种环及多个环的并。','图由本报告代码直接绘制。']):C.drawString(195,140-23*j,s)
def foot(c,doc):
 c.setStrokeColor(HexColor('#bccbd2'));c.line(43,38,552,38);c.setFont('Chinese',8);c.drawString(43,25,'Q9 | GitHub 方法延伸 | 2026-10-30 | 未完成 Lean 重放');c.drawRightString(552,25,str(doc.page))
p('Q9 snake-in-the-box\n交叉评审与计算证明','title')
p('研究基线：research/unconditional-241。路线：项目的局部窗口、空面计数、全局计费、CNF 与可重放证明。本次不使用 Ramsey 方法。')
p('本次严格取得的结果','h')
p('对每个内部顶点，得到整数评分 q≥23：先用完整、可独立检查的 CNF/RUP 证书排除 q≤21，再由项目的 singleton-square 结论和普通数学推导排除 q=22。证书自身仍只标为 q≥22。')
p('尚未取得：新的 a(9) 数值上界；三中心阈值 255 或 267；本机 Lean 内核认证。两类三中心 cap=254 查询均为 UNKNOWN。本报告不把中间学习子句、历史回执或启发式当作新上界。')
p('计算证据','h')
p('单中心：4,007 变量，116,350 子句，其中 77,868 条有效八环割；7,621 条 RUP 步骤，1,604,124 条单位传播提示，最终空子句独立检查通过。另导出标准压缩 DIMACS 与正提示 LRAT。')
p('代码工作：实现可用的纯 Python CDCL 后端；修复范围检查与证书标签错误；采用根传播后的 watch 重建、集合查重、可恢复检查点；与一个子智能体反复互评六轮以上。')
p('阅读范围：本报告给出新的计费引理、局部证书的语义桥、八环枚举完备性、目标上界的条件算术以及未解阻碍。完整程序、证明提示、评审记录和已有 Lean 源码随 ZIP 提供。','small')
page('1  定义与全局计费恒等式')
p('Q9 的顶点为 0…511，邻接当且仅当二进制异或有一位为 1。snake 是诱导路径 S：任意两顶点邻接当且仅当它们在路径上相邻。记 v=|S|，边数 m=v−1；本报告所有 a(9) 数值目标指边数。以下全局恒等式假设 v≥2（m≥1）。')
p('坐标 k-face 是固定 9−k 个坐标的子立方体。α(x) 是通过选中点 x、且其他三个顶点均不在 S 中的坐标方形数。e₂(x)、e₃(x) 分别为空方形、空三维面与 x 的最小图距离为 1 的数量。')
p('对距离 x 为 1 的空方形 F，有 7 个母三维面；h(F) 是其中非空者的数量。通过 x 的母面唯一，记其选中点数为 tₓ(F)。所有选中点位于与 F 相对的方形，故 1≤t≤3；取 4 会使选中集含整个方形。')
p('a(x)=α(x)+Σ[F 空且 dist(x,F)=1] 2/(h(F)tₓ(F))','eq')
p('每个被支配的空方形 F，在它的每个非空母面内向 t 个选中点各给 2/(ht)，总计给 2。不同母面的对面互不相交。令 U 是未被任何选中点支配的空方形数，s₀ 是空方形总数，T=Σα，则 Σa=T+2(s₀−U)。')
p('Q9 有 C(9,2)·2⁷=4608 个方形，每点在 36 个方形上。记 sⱼ 为含 j 个选中点的方形数。诱导路径没有 s₄；且 s₃=v−2：每个内部点的两条路径边唯一确定一个三点方形，反之三点方形的中心是内部点。')
p('Σsⱼ=4608，Σj sⱼ=36v，T=s₁。消去 s₂ 得\nT+2s₀=9216−36v+s₃=9214−35v。\n因此 Σa(x)=9214−35v−2U≤9214−35v。','eq')
page('2  新评分及完整局部不等式')
p('令 C₁(x) 是通过 x 且只有 x 被选中的三维面数；C₂,d(x) 是通过 x、恰有两个选中点且两者距离为 d 的三维面数。定义 V=12C₁+2C₂,₁+C₂,₂。距离 3 的二点构形贡献为零。')
p('q(x)=21α(x)+2e₂(x)+e₃(x)+V(x)。\n对每个真正 snake 的选中点，q(x)≤21a(x)。','eq')
p('证明步骤一。D(x)=Σ_F(7−h(F))=3e₃(x)。左边数空方形 F 与其空母面 R 的对；这样的 R 距 x 为 1，其唯一最近顶点包含在恰好三个二维面中。反向构造唯一，故恰为三重计数。由于 h≥1，还得到 3e₃≤6e₂。')
p('步骤二。设 B=[t≤2]，C=[t=1]，则 1/t=(2+B+3C)/6。对整数 h=1…7，\n2/(3h)−(13−h)/63=(h−6)(h−7)/(63h)≥0。\n因此 2/(ht)≥(2+B+3C)(13−h)/126。')
p('步骤三。因 13−h≥6，把右边拆开得 (13−h)/63+(B+3C)/21。求和后，第一部分是 (6e₂+D)/63=(2e₂+e₃)/21。')
p('步骤四。E₁=ΣC=3C₁，E≤₂=ΣB=3C₁+2C₂,₁+C₂,₂：单点三维面给出三个相对空方形；二点距离 d 的三维面有 3−d 个坐标在两点上取值相同，每个给一个空方形。因此 E≤₂+3E₁=V，且 0≤V≤4e₂。合并即得 q≤21a。')
p('全局求和还得到如下严格关系。Bⱼ=Σeⱼ；N₁、N₂,d 是整个 Q9 中相应低占用三维面的数量：')
p('21T+2B₂+B₃+12N₁+4N₂,₁+2N₂,₂\n≤21(9214−35v)。','eq')
p('这是有效的组合不等式。要从它收紧数值上界，还需要足够强的普适窗口下界；样本上的大评分不能代替该步骤。','small')
page('3  单中心计算证明与语义桥')
p('取任意内部顶点及其前后邻点。平移并置换坐标，可标准化为 [0,1,17]，中心为 1。q 的所有指标仅依赖中心半径 4 的点。每个真实 snake 在该球上的限制，都满足原项目 Encoding 的必要条件：固定窗口、选中点度≤2、内部点无孤立、端点预算≤2、禁四环和六环。')
p('使用原始 wincert.py 中 Encoding 类，不修改几何子句；指标由双向布尔门定义；加法器及比较器精确编码 q≤21。每个真实 snake 都能扩展为这些辅助门变量的满足赋值。再加入球内每个诱导八环的“不能全选”子句：它们对真实诱导路径必然成立。')
p('完整公式 116,350 子句被证书排除。独立检查器从原始子句出发，逐条否定学习子句，并按证书给出的较早子句编号做单位传播；每一步均到矛盾后才加入学习子句，最后检查空子句。因此该公式不可满足，真实内部顶点必有 q≥22。')
p('额外严格推论 q≥23。沿用项目 singleton-square 引理 α≥1。若 q=22，整数性迫使 α=1 且 2e₂+e₃+V=1，所以 e₂=0。由 3e₃≤6e₂ 得 e₃=0，由 V≤4e₂ 得 V=0，矛盾。')
p('认证范围：RUP/LRAT 检查、原始 CNF 重建和几何割验证均已完成；singleton 与 endpoint 引理的既有 Lean 源码已查读，本机未重新运行 Lean。本报告没有把 Python 检查称为 Lean 内核检查。')
p('源码标识：wincert.py SHA256\n346cc64a58d475a51d4a1622c549c79426035e8df014ebd7bc42097067b9ff01','small')
p('文件：certificate/manifest.json；pointwise_score22.cnf.gz；pointwise_score22.lrat.gz；cycle8_geometry.json.gz。运行 verify_certificate.py --rebuild 会重新构造原项目 CNF、逐一检查八环、核对全部子句并重放证明。','small')
page('4  八环枚举为何完备；长环仍是障碍')
story.append(CycleFigure())
p('一个诱导八环中，每个坐标翻转偶数次。至多用 4 个坐标；若至多 3 个，则只能位于 Q3，八个顶点全选会产生度 3 与弦。因此恰用 4 个坐标且各翻转两次，所属四维面唯一。')
p('每个 Q4 有 168 个诱导八环顶点集，程序枚举其全部 C(16,8)=12,870 个候选并直接检查连通性及诱导度 2。Q9 有 C(9,4)·2⁵=4032 个四维面，所以总数为 677,376。两套独立生成方法给出完全相同的 168 个 Q4 模板，并独立核对球内计数；未比较两套完整 Q9 全集。')
p('单中心半径 4 球内计数：设四维面的固定外坐标相对球心有 k 个 1，则只允许自由部分权重≤4−k。Q4 的 168 个八环中，k=0,1,2 时分别剩 168,84,3 个，k≥3 为 0。故总数为 C(9,4)(168+5·84+10·3)=77,868。完整列表随证书提供。')
p('固定三点窗口的 rooted 八环还有独立较小枚举：选择两条额外坐标，在剩余六步中枚举两次重复的翻转词；3,780 个词候选最终得到 294 个不同诱导八环，与 DFS 完全一致。这些检查辅助验证枚举器，不替代完整球内割。')
p('局部满足赋值的反例：原几何条件在 cap21 时允许由八环、边界孤立点及短路径拼出的选中集。禁完八环仍不意味着全局只有一条路径；更长的环并可能通过窗口检查。本程序把每个实际发现的完整诱导环逐一验证后才加割。半径 9 保证覆盖全部 512 点（多中心球的联合可能更早覆盖）；小球内无环的 SAT 也不能直接叫作全局 snake。')
p('限制：q≥23 是局部证书及计费推论；它本身远不足以超过既有数值上界。三中心目标必须同时排除两类方向窗口，且不能把长环并的局部模型误作真正路径。')
page('5  234 与 233 的精确条件目标')
p('连续三个内部中心连同前后点构成四个方向翻转。诱导性使前三方向各异；第四方向只能回到第一方向或使用新方向。所以只有 0120 与 0123 两类。独立枚举 9⁴ 个方向词得到对应 504 和 3024 个有效窗口，除此之外无其他形状。')
p('项目 endpoint_alpha_ge_four 证明每个端点 α≥4。其 EndpointFourWitness.lean 给出 120 边真实 snake 达到端点 α=4；本次重新解析列表并检查所有点对。因此当前不能擅自把端点常数提高。')
p('假设这两类真实三中心窗口均满足 Σq≥H。把 v−2 个内部点分成 k=floor((v−2)/3) 个不重叠三元组和 r=(v−2) mod3 个剩点，用较弱但已证 q≥22 即有：')
p('Σa≥8+(Hk+22r)/21。\n必要条件：735v+H floor((v−2)/3)+22((v−2) mod3)≤193326。','eq')
p('若 H=255，则在 v=236 时超出右边 24，即实际计费差为 8/7。上式随 v 增加，差的增量分别为 757 或 735+H−44，均正；故排除全部 v≥236，得到边数 m≤234。需要两个 cap254 查询都完成 UNSAT。')
p('若 H=267，则在 v=235 时超出右边 2，差为 2/21，足够推出 m≤233。无需先前设想的 268。若用 q≥23 处理两剩点，差为 4/21。两个 cap266 查询仍未证明。')
p('当前 cap254 的 binary 检查点：\n0120：173,531 静态子句；28,242 已检 RUP 步，2,708,052 提示。\n0123：173,106 静态子句；25,935 已检 RUP 步，2,852,769 提示。\n两者均无空子句、无完整满足模型，结论为 UNKNOWN。','eq')
p('以上 234、233 是明确、可验证的条件目标，不是新上界声明。历史分支的 235–237 回执也没有在本机完成首次从源重建。')
page('6  编码优化、互评发现与复现')
p('纯 Python CDCL 使用 watched literals、first-UIP 学习、活动度、相位与重启。每条学习子句附正编号 RUP 提示，交给独立小检查器核验。超时只保存已检学习子句及启发式；下一片从完整 CNF 重建逻辑状态。添加新几何割后丢弃旧学习前缀，避免子句编号改变。')
p('已实施优化：根单位传播后只给活动子句重建 watch；重言式检查改用缓存集合；gzip 检查点一次编码写入；不反复全检已确认前缀。一次相同前缀的初始化 profile 从 20.53 秒降为 6.21 秒（约 3.31 倍，仅该初始化样本，不是总求解加速保证）。')
p('互评中的真实修复：① 八环校验未拒绝超出维度的顶点，现补整数、范围及负例检查。② 可配置输入的导出器把 cap0 证明也标成 score22，现限制 cap21、单中心、完整目标和半径范围，并在导出与验证两端拒绝 10 个标签突变负例。')
p('GT 实验：正权 generalized totalizer 旨在增强阈值传播，但辅助变量只要求存在，不能当作等价门取反。独立证明按树归纳：超阈值强制根 overflow；未超阈值的真实子树和给出满足扩展。作者穷举 1736 次输入；主智能体另检 1920 次相关输入，并对 832 个超阈值输入独立求解、核验 RUP。')
p('GT 在两类真实查询新增约 611,000 条 PB 子句，binary 约 28,000 条；含同样八环割，总规模约 756,000 对 173,000。两个 fresh 10 秒短测均 UNKNOWN，新增 1859 / 1318 条 RUP 步全部核验，总墙钟约 15.9 / 16.0 秒。完整查询在 GT_probes；不可与累计 binary 搜索直接比较速度。详见 GT_ENCODING.md 与实际 JSON。')
p('复现（ZIP 解压后，在 work/branch241-review）：\npython verify_certificate.py --rebuild\npython gt_root_review.py\npython triple_bound_arithmetic.py\npython research_loop.py --dirs 0120 --cap 254 --all8 --static8-fold --seconds 60 --slice-seconds 10 --out loop_k3_cap254_r4_d0120_all8\n第二形状把 0120 改为 0123。保留原目录层级以定位项目源码。','small')
p('输出附完整图代码、本报告生成器、普通数学证明、源代码、现有 Lean 文件、测试和评审记录、标准证书及可继续的检查点。下一步需要更强的窗口传播或全局连通性约束，并最终走项目 Lean 认证链；本次未完成部分明确保留为研究阻碍。','small')
SimpleDocTemplate(str(OUT/'Q9_Peer_Review_Report.pdf'),pagesize=(595.28,841.89),rightMargin=43,leftMargin=43,topMargin=45,bottomMargin=50,title='Q9 Peer Review and Checked Local Certificate',author='Research continuation').build(story,onFirstPage=foot,onLaterPages=foot)
print(OUT/'Q9_Peer_Review_Report.pdf')
