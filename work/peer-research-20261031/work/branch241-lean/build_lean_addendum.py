from pathlib import Path
import json
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.colors import HexColor
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from xml.sax.saxutils import escape
H=Path(__file__).resolve().parent;ROOT=H.parents[1];D=ROOT/'outputs/branch241_lean_20261030';D.mkdir(parents=True,exist_ok=True)
pdfmetrics.registerFont(TTFont('Chinese','C:/Windows/Fonts/simsun.ttc',subfontIndex=0))
styles={'title':ParagraphStyle('t',fontName='Chinese',fontSize=24,leading=33,spaceAfter=18,textColor=HexColor('#16384c')),'h':ParagraphStyle('h',fontName='Chinese',fontSize=17,leading=24,spaceAfter=14,textColor=HexColor('#16384c')),'p':ParagraphStyle('p',fontName='Chinese',fontSize=11,leading=18,spaceAfter=12),'eq':ParagraphStyle('eq',fontName='Chinese',fontSize=10,leading=17,spaceAfter=14,spaceBefore=4,backColor=HexColor('#edf4f7'),borderPadding=8),'s':ParagraphStyle('s',fontName='Chinese',fontSize=9,leading=14,spaceAfter=9)}
a=[]
def p(t,k='p'):
 t=t.translate(str.maketrans({'−':'-','₀':'0','₁':'1','₂':'2','₃':'3'}))
 a.append(Paragraph(escape(t).replace('\n','<br/>'),styles[k]))
def page(t):a.append(PageBreak());p(t,'h')
def foot(c,d):
 c.setStrokeColor(HexColor('#bdcbd3'));c.line(43,39,552,39);c.setFont('Chinese',8);c.drawString(43,25,'Q9 | Lean 4.19.0 实际验证增补 | 2026-10-30');c.drawRightString(552,25,str(d.page))
p('Q9 研究 · Lean 验证增补','title')
p('本次实际执行了 Lean 4.19.0 检查，而不只是生成 Lean 源码。验证通过的部分包括评分算术、抽象计费不等式、小规模 Q9 几何和适配后的 LRAT 检查器测试。完整单中心证书及其几何桥尚未完成 Lean 认证。')
p('执行环境与公理审计','h')
p('本机官方 Windows 工具链被系统应用程序控制策略阻止运行；未绕过该策略。改用 Lean 官方 live.lean-lang.org 的 lean-v4.19.0 项目，通过其 Lean4web/LSP 接口提交小型源码并接收完整诊断。服务返回版本 4.19.0，与项目固定版本一致。')
p('七个验证单元通过。去重后为 23 个数学／有限几何／必要前提反例定理，以及 20 个 LRAT 检查器及测试结论。逐条 #print axioms 审计：无公理，或仅有 propext、Classical.choice、Quot.sound；无 sorryAx。全部源码哈希与收到的检查日志绑定。')
p('通过的内容','h')
p('ScoreAlgebra：9 个定理。系数表、评分 22→23 的条件推论、方形计数恒等式的代数消元、234/233 的条件排除，以及临界点差值 24 和 2。')
p('ScoreCharges：7 个定理。精确整数比例、逐项计费表、任意列表求和归纳、60q≤1260a 的抽象形式、空方形母面占用预算。两个几何计数恒等式仍明确作为参数。')
p('FiniteGeometry：5 个实际 Q9 布尔几何结论。三中心方向限制、最后方向表，以及所绘八环的顶点互异、范围和无弦邻接关系。NegativeControls 另有 2 个定理证明不能删去关键前提。')
p('适配 LRAT：小矛盾 CNF、变量 4007、子句编号 70000、300 字面量学习子句均通过内核重放；缺失提示与对可满足 CNF 的伪反证被拒绝。刻意声称 False 或错误 LRAT 成功的两个独立输入，也都产生错误及 sorryAx，验证流程将其判为拒绝。')
page('1  精确的已证命题与尚未接上的前提')
p('评分推论的 Lean 类型','h')
p('scoreGap23(alpha,e2,e3,V : Nat)\n(1≤alpha) → (3e3≤6e2) → (V≤4e2) →\n(22≤21alpha+2e2+e3+V) →\n23≤21alpha+2e2+e3+V','eq')
p('该定理本身没有假装证明 cap21 的 CNF 排除。22≤q 是明确参数；singleton 引理及两个几何计数不等式与实际 snake 的连接，还需要 Lean 几何桥。去掉 SAT 前提或 singleton 前提均有明确数值反例，且反例的不成立陈述也已在 Lean 中证明。')
p('计费不等式的整数形式','h')
p('对每个空方形关联项，h∈{1,…,7}，t∈{1,2,3}。Lean 证明 2520/(ht) 是精确整数，并验证逐项下界：\n2520/(ht)≥20(13−h)+60([t≤2]+3[t=1])。')
p('把任意关联项列表求和，使用显式参数 Σ(7−h)=3e₃ 与 Σ([t≤2]+3[t=1])=V，Lean 得到：\n60(21α+2e₂+e₃+V)≤1260α+Σ2520/(ht)。\n右边恰对应 1260a；“列表确实枚举了实际 snake 的相关空方形”尚未在 Lean 中构造。','eq')
p('234 与 233 仍为条件定理','h')
p('conditional234：若\n735v+255floor((v−2)/3)+22((v−2) mod3)≤193326，\n则 v≤235，即边数≤234。\nconditional233 把 255 换为 267，得到 v≤234，即边数≤233。','eq')
p('Lean 已证明上述整数推理，尚未证明任意三中心窗口都有 q 和至少 255 或 267。现有两个 cap254 搜索仍 UNKNOWN。因此没有新增数值上界，也没有把条件结论改名为无条件结论。')
page('2  完整 LRAT 重放准备与剩余认证链')
p('适配限制已被实际测试','h')
p('原检查器不能直接装入本证书：本次有 4007 个变量，需要 literal offset=5000；116350 条初始子句超出旧分树格式范围，需要 18 位字和分树标志 131072；最长学习子句为 1548 个字面量，解析 fuel 从 255 提至 2048。提示上限 4095 也进行了数据预检。')
p('适配器沿用项目的检查器健全性证明。56–69 KB 的独立测试源码已在官方 Lean 4.19.0 执行；通过结果只覆盖检查器证明与测试，不能替代大证书逐步求值。')
p('完整证书保留全部 116350 条初始子句及原顺序，含 7621 个 RUP 步骤和 1604124 条单位提示。已生成分块 Lean 回放源码，并再次通过 Python RUP 检查及格式模拟；完整 Lean 源码明确标记 UNREPLAYED。公共在线环境只用于上述小规模验证，没有提交巨大回放任务。')
p('尚未完成的两层','h')
p('第一层：在允许运行 Lean 的机器上，完成所有生成回放模块及最终 Unsat 定理的内核编译和公理审计。本机应用程序控制策略阻止这一原生计算；在线的小测试不补足该缺口。')
p('第二层：把实际 snake、窗口坐标标准化、空面／占用指标、辅助变量赋值、每类几何与八环子句的正确性，以及 q 的数值目标接到确切 CNF。即使第一层通过，第二层未完成前，也只能声称某个具体 CNF 在 Lean 中不可满足，不能称完整 snake 定理已认证。')
p('复现材料','h')
p('核对本次在线诊断、源码哈希、公理与负例：\npython work/branch241-lean/check_remote_receipts.py\n小模块可直接在安装 Lean 4.19.0 的环境编译。独立在线复验入口：\nnode work/branch241-lean/tools/remote_lean.mjs SOURCE.lean LOG.json\n该脚本只接受完成标记、准确版本且无错误／警告／sorryAx 的返回。刻意错误输入应退出失败。','s')
p('离线全证书的编译计划、分块源码、构建驱动与详细 manifest 随 ZIP 提供。运行前先查看计划，不重建已有未变化模块；可恢复日志按源码和依赖哈希校验。离线源码的生成状态与实际在线通过状态分别记录，不能互换。','s')
p('本增补应与上一份 Q9_Peer_Review_Report.pdf 一起阅读。先前 Python 证书及普通数学结果没有被撤回；本次新增的是准确分层的 Lean 认证进度。','s')
SimpleDocTemplate(str(D/'Q9_Lean_Verification_Addendum.pdf'),pagesize=(595.28,841.89),leftMargin=43,rightMargin=43,topMargin=45,bottomMargin=52,title='Q9 Lean 4.19.0 Verification Addendum').build(a,onFirstPage=foot,onLaterPages=foot)
print(D/'Q9_Lean_Verification_Addendum.pdf')
