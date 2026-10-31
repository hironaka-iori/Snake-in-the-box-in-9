from pathlib import Path
from reportlab.pdfgen import canvas
from reportlab.lib.pagesizes import A4,landscape
from reportlab.platypus import Paragraph
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib.colors import HexColor
from xml.sax.saxutils import escape
H=Path(__file__).resolve().parent;O=Path.cwd()/'outputs/global_cycle_compression_20261031';O.mkdir(exist_ok=True)
pdfmetrics.registerFont(TTFont('Song','C:/Windows/Fonts/simsun.ttc',subfontIndex=0))
b=ParagraphStyle('body',fontName='Song',fontSize=11,leading=18,spaceAfter=10,textColor=HexColor('#18334b'))
small=ParagraphStyle('small',parent=b,fontSize=9,leading=14)
C=canvas.Canvas(str(O/'Q9_Critical_Cycle_Upper_Bound_Update.pdf'),pagesize=A4);C.setTitle('Q9 critical-cycle exclusions and upper-bound arithmetic');C.setAuthor('Local research and independent mathematical review')
page=0;Y=0;W=0;HH=0;current=''
def footer():
 C.setFont('Song',9);C.setFillColor(HexColor('#64748b'));C.drawString(48,25,'2026-10-31 | 本地研究快照；未上传；未宣称新全局上界');C.drawRightString(W-48,25,str(page))
def new(title,wide=False):
 global page,Y,W,HH,current
 if page:footer();C.showPage()
 page+=1;W,HH=landscape(A4) if wide else A4;C.setPageSize((W,HH));current=title;Y=HH-50;C.setFillColor(HexColor('#123a5a'));C.setFont('Song',19);C.drawString(48,Y,title);Y-=32;C.setStrokeColor(HexColor('#d9e6f2'));C.line(48,Y,W-48,Y);Y-=22
def para(s,style=b):
 global Y
 p=Paragraph(s,style);w,h=p.wrap(W-96,1000)
 if Y-h<55:new(current+'（续）')
 p.drawOn(C,48,Y-h);Y-=h+11

def eq(s):
 global Y
 if Y<90:new(current+'（续）')
 C.setFillColor(HexColor('#eef5fb'));C.roundRect(48,Y-32,W-96,35,5,fill=1,stroke=0);C.setFillColor(HexColor('#123a5a'));C.setFont('Courier',10);C.drawString(59,Y-17,s);Y-=47
new('Q9：临界环排除与上界推导改进')
para('<b>结论与证据边界。</b> 已严格排除当前有限模型中一个均值 480 的四步环连续经过七条边的历史；这给出新的长窗口禁形和只增加 24 个状态的历史扩展。尚未重算完整模型的均值，也没有新的全局数值上界。')
para('输入是仓库 milestone 72 的 proved-analysis / proved-model 快照：1,601,856 个状态、4,957,613 条转移，均值 480，势函数范围 578。仓库报告全局区间 191 至 235；这是继承的状态，本轮没有重新回放该全局定理。其有限模型到任意 snake 的完整解释仍标为待完成。')
para('<b>1. 精确算术门槛。</b> 设 m 是边数。以下推导以项目给出的不等式和端点常数正确为前提，不把识别出公式当作几何桥的证明。设整数 p,d 为正，mu=p/d，R 为同一整数尺度下的势差范围：')
eq('m <= (1098960*d + 8*p + R) / (p + 4200*d)')
para('要排除 235 边，右侧必须严格小于 235。分母为正，移项后等价于：')
eq('227*p > 111960*d + R')
para('当 d=1、R=578 时，需要 mu &gt; 112538/227，约 495.762115。整数均值 496 足够；495 不够。实际新势函数的 R 必须重新计算，不能沿用旧范围作为假设。')
eq('mu=496, R=578: m <= 551753/2348 < 235')
para('若 mu=496，新范围必须满足 R &lt; 632，整数 R 至多 631。若均值仍为 480，即使 R 降到零也不足以排除 235，因为 227*480 &lt; 111960。仅优化旧势函数的边界范围无法到达下一整数界。')
new('2. 从模型四步环到真实立方体的弦')
para('四个转移依次为 3416157、1822955、734195、4462580，权重依次为 480、360、600、480，总和 1920，环均值 480。它们分别携带九步规范化方向字：')
for s in ['0 1 2 3 4 2 1 5 0','0 1 2 3 1 0 4 5 0','0 1 2 0 3 4 5 3 0','0 1 2 3 4 5 3 2 0']:eq(s)
para('<b>重叠唯一性。</b> 相邻窗口共享八个方向。每个后继字的前八位已经包含全部六个标签，所以抽象标签到实际坐标的映射被重叠完全确定且为单射；末位没有选择新坐标的自由。初始六个标签可嵌入 Q9 的任意六个不同坐标，这只改变坐标命名，不改变 Hamming 距离。')
para('<b>拼接计算。</b> 从相位零拼接，实际方向成为周期八的字 0,1,2,3,4,2,1,5 的重复。七条模型边提供 9+(7-1)=15 个实际方向，其 XOR 为 32，即第六个单位坐标。相位一、二、三的 XOR 分别为 32、8、4，也均为单位向量。')
para('因此第零个与第十五个顶点相邻，而它们在路径上相隔十五条边，构成不允许的弦。独立程序还逐对检查：这四个十五步字中唯一的非连续距离不超过一的顶点对都是 (0,15)。前十四步仍是合法诱导路径。故本论证不能禁止六条模型边，也不能删除单条转移或只禁止一次四步绕环。')
para('<b>一般周期引理。</b> 对任意 p≥2，若实际坐标字以周期 p 重复，则两份完整周期的 XOR 为零。去掉最后一个方向后，前 2p-1 步的 XOR 就是该方向对应的单位向量。两个端点在路径距离至少三处相邻，故不可能是诱导路径。此引理要求实际坐标周期；抽象状态周期本身并不够，必须先证明重叠映射。')
new('3. 可复现的几何障碍',True)
C.drawImage(str(H/'figures/critical_cycle_chord.png'),48,100,width=W-96,height=(W-96)*790/1420,preserveAspectRatio=True,mask='auto')
C.setFont('Song',10);C.setFillColor(HexColor('#334155'));C.drawString(48,73,'图中编号为路径索引，v 为实际立方体顶点整数。红边是非连续首尾之间的弦。完整 SVG 与制图代码见代码包。')
new('4. 安全的历史扩展：增加 24 个状态')
para('只把原环的四个顶点分裂。每个顶点新增 run=1 至 6 的六份状态，原状态作为 run=0，其他顶点不变。因此状态数增加 4*6=24，成为 1,601,880；实际新增边数依这四个顶点的出度而定，未在缺失的完整图上测量。')
para('<b>转移规则。</b> 对这四个已注册转移 ID，run 加一；从 run=6 再沿任意注册边的转移被省略。所有非注册边都把目标计数重置为零，包含从环顶点离开、回到环、平行边及自环等情况。权重由原边原样继承。')
para('<b>保留性证明。</b> run 的不变量是到当前为止连续经过注册边的次数。注册子图恰是一条简单四环，故七条连续注册边恰对应四个相位之一的七边禁历史。真实 snake 不可能包含这些历史，故其映射游走的计数始终不超过六，并能在扩展图中继续。反之，每条扩展边都投影到原边。')
para('原势函数可以沿投影拉回到每个扩展状态。若旧模型的均值 480 势不等式已成立，拉回后仍逐边成立，范围不变；因此该扩展不破坏已有下界证书。但这不证明新均值严格大于 480：其他临界环可能幸存。')
para('<b>必须重新计算的部分。</b> 要得到 234，须重新求并独立检验全部扩展转移的均值与势函数，再验证 227p &gt; 111960d+R，并补齐从任意 snake 到图游走的解释及正式认证。当前只有一个临界环历史被排除，不能声称所有临界分量已覆盖。')
new('5. 复核结果、限制与复现入口')
para('<b>已通过：</b> 四个相位的坐标重叠和全顶点对检查；9,837 个短周期字的 XOR 恒等式控制；825 条基础 toy 游走；另一个独立程序的 15,840 条带分支、平行边和自环的 toy 游走及 65 项逐状态转移检查。')
para('<b>反过度推断控制：</b> toy 模型中，切断唯一低均值环可使均值由 480 变成 720；加入一个未受影响的均值 480 环后，新图均值仍是 480。这是演示“去掉一个取等环不保证全模型均值增加”的反例，不是实际模型的计算结果。')
para('<b>尚未执行：</b> 4,957,613 条真实转移的完整扩展与均值重算。完整 NPZ 图不是本地现有文件；本机 NumPy 扩展被应用程序控制策略阻止。NPZ 适配器仅做静态审查，执行状态为 BLOCKED。本轮没有进行新的 Lean 内核验证，也没有上传仓库。')
para('<b>前缀剪枝不能直接求和。</b> 之前的单分支 131 后缀容量只排除对应前缀。不同窗口的缺失顶点可能重叠，直接相加会重复收费。合法替代是对每个禁形组给非负有理权重，并逐顶点核验总覆盖不超过一；这样可证明缺失顶点数至少为加权损失之和的上取整。该对偶仍然只是固定残余图的容量界，除非另有全局覆盖证明。')
para('<b>标准库复现：</b> history_lift.py；check_attaining_cycle.py；review_lift_stdlib.py；check_aggregate_review.py。后者的完整复现说明及路径见 README。make_cycle_figure.py 另需 Pillow 与 Segoe UI 字体。NPZ 适配器 apply_npz_lift.py 需要可用 NumPy 和与冻结 SHA256 一致的真实输入图。')
para('上游材料：milestones/72-four-count-proof-closure/README.md、data/proved-analysis.json、data/proved-model.json。完整证明、独立评审、精确数据和源程序均保存在同目录及交付 ZIP。',small)
footer();C.save();print(O/'Q9_Critical_Cycle_Upper_Bound_Update.pdf')
