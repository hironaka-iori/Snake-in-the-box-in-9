import B112E256Inputs
namespace B112E256
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1844 : List Lit := [(83, false), (85, false), (87, false)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c535, c537] c1844 (by decide) p (sat_cons (step535 p h) (sat_cons (step537 p h) (sat_nil p)))
def c1845 : List Lit := [(4, false)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c771, c15] c1845 (by decide) p (sat_cons (step771 p h) (sat_cons (step15 p h) (sat_nil p)))
def c1846 : List Lit := [(502, false)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c1096, c1093] c1846 (by decide) p (sat_cons (step1096 p h) (sat_cons (step1093 p h) (sat_nil p)))
def c1847 : List Lit := [(378, false)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c1096, c1095] c1847 (by decide) p (sat_cons (step1096 p h) (sat_cons (step1095 p h) (sat_nil p)))
def c1848 : List Lit := [(500, false)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c1846, c1089] c1848 (by decide) p (sat_cons (step1846 p h) (sat_cons (step1089 p h) (sat_nil p)))
def c1849 : List Lit := [(438, false)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c1846, c1092] c1849 (by decide) p (sat_cons (step1846 p h) (sat_cons (step1092 p h) (sat_nil p)))
def c1850 : List Lit := [(376, false)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c1847, c971] c1850 (by decide) p (sat_cons (step1847 p h) (sat_cons (step971 p h) (sat_nil p)))
def c1851 : List Lit := [(314, false)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c1847, c974] c1851 (by decide) p (sat_cons (step1847 p h) (sat_cons (step974 p h) (sat_nil p)))
def c1852 : List Lit := [(498, false)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c1848, c1084] c1852 (by decide) p (sat_cons (step1848 p h) (sat_cons (step1084 p h) (sat_nil p)))
def c1853 : List Lit := [(468, false)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c1848, c1087] c1853 (by decide) p (sat_cons (step1848 p h) (sat_cons (step1087 p h) (sat_nil p)))
def c1854 : List Lit := [(436, false)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c1849, c1025] c1854 (by decide) p (sat_cons (step1849 p h) (sat_cons (step1025 p h) (sat_nil p)))
def c1855 : List Lit := [(406, false)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c1849, c1028] c1855 (by decide) p (sat_cons (step1849 p h) (sat_cons (step1028 p h) (sat_nil p)))
def c1856 : List Lit := [(374, false)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c1850, c966] c1856 (by decide) p (sat_cons (step1850 p h) (sat_cons (step966 p h) (sat_nil p)))
def c1857 : List Lit := [(344, false)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c1850, c969] c1857 (by decide) p (sat_cons (step1850 p h) (sat_cons (step969 p h) (sat_nil p)))
def c1858 : List Lit := [(312, false)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c1851, c901] c1858 (by decide) p (sat_cons (step1851 p h) (sat_cons (step901 p h) (sat_nil p)))
def c1859 : List Lit := [(282, false)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c1851, c904] c1859 (by decide) p (sat_cons (step1851 p h) (sat_cons (step904 p h) (sat_nil p)))
def c1860 : List Lit := [(496, false)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c1852, c1079] c1860 (by decide) p (sat_cons (step1852 p h) (sat_cons (step1079 p h) (sat_nil p)))
def c1861 : List Lit := [(482, false)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c1852, c1082] c1861 (by decide) p (sat_cons (step1852 p h) (sat_cons (step1082 p h) (sat_nil p)))
def c1862 : List Lit := [(466, false)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.LocalRup.prove_clause [c1853, c1051] c1862 (by decide) p (sat_cons (step1853 p h) (sat_cons (step1051 p h) (sat_nil p)))
def c1863 : List Lit := [(452, false)]
theorem step1863 (p : Nat → Bool) (h : Constraints p) : clause p c1863 = true :=
  Snake9.LocalRup.prove_clause [c1853, c1054] c1863 (by decide) p (sat_cons (step1853 p h) (sat_cons (step1054 p h) (sat_nil p)))
def c1864 : List Lit := [(404, false)]
theorem step1864 (p : Nat → Bool) (h : Constraints p) : clause p c1864 = true :=
  Snake9.LocalRup.prove_clause [c1855, c1000] c1864 (by decide) p (sat_cons (step1855 p h) (sat_cons (step1000 p h) (sat_nil p)))
def c1865 : List Lit := [(390, false)]
theorem step1865 (p : Nat → Bool) (h : Constraints p) : clause p c1865 = true :=
  Snake9.LocalRup.prove_clause [c1855, c1003] c1865 (by decide) p (sat_cons (step1855 p h) (sat_cons (step1003 p h) (sat_nil p)))
def c1866 : List Lit := [(372, false)]
theorem step1866 (p : Nat → Bool) (h : Constraints p) : clause p c1866 = true :=
  Snake9.LocalRup.prove_clause [c1856, c962] c1866 (by decide) p (sat_cons (step1856 p h) (sat_cons (step962 p h) (sat_nil p)))
def c1867 : List Lit := [(342, false)]
theorem step1867 (p : Nat → Bool) (h : Constraints p) : clause p c1867 = true :=
  Snake9.LocalRup.prove_clause [c1857, c932] c1867 (by decide) p (sat_cons (step1857 p h) (sat_cons (step932 p h) (sat_nil p)))
def c1868 : List Lit := [(328, false)]
theorem step1868 (p : Nat → Bool) (h : Constraints p) : clause p c1868 = true :=
  Snake9.LocalRup.prove_clause [c1857, c935] c1868 (by decide) p (sat_cons (step1857 p h) (sat_cons (step935 p h) (sat_nil p)))
def c1869 : List Lit := [(310, false)]
theorem step1869 (p : Nat → Bool) (h : Constraints p) : clause p c1869 = true :=
  Snake9.LocalRup.prove_clause [c1858, c896] c1869 (by decide) p (sat_cons (step1858 p h) (sat_cons (step896 p h) (sat_nil p)))
def c1870 : List Lit := [(296, false)]
theorem step1870 (p : Nat → Bool) (h : Constraints p) : clause p c1870 = true :=
  Snake9.LocalRup.prove_clause [c1858, c899] c1870 (by decide) p (sat_cons (step1858 p h) (sat_cons (step899 p h) (sat_nil p)))
def c1871 : List Lit := [(280, false)]
theorem step1871 (p : Nat → Bool) (h : Constraints p) : clause p c1871 = true :=
  Snake9.LocalRup.prove_clause [c1859, c865] c1871 (by decide) p (sat_cons (step1859 p h) (sat_cons (step865 p h) (sat_nil p)))
def c1872 : List Lit := [(266, false)]
theorem step1872 (p : Nat → Bool) (h : Constraints p) : clause p c1872 = true :=
  Snake9.LocalRup.prove_clause [c1859, c868] c1872 (by decide) p (sat_cons (step1859 p h) (sat_cons (step868 p h) (sat_nil p)))
def c1873 : List Lit := [(488, false)]
theorem step1873 (p : Nat → Bool) (h : Constraints p) : clause p c1873 = true :=
  Snake9.LocalRup.prove_clause [c1860, c1077] c1873 (by decide) p (sat_cons (step1860 p h) (sat_cons (step1077 p h) (sat_nil p)))
def c1874 : List Lit := [(480, false)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c1861, c1063] c1874 (by decide) p (sat_cons (step1861 p h) (sat_cons (step1063 p h) (sat_nil p)))
def c1875 : List Lit := [(402, false)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c1864, c996] c1875 (by decide) p (sat_cons (step1864 p h) (sat_cons (step996 p h) (sat_nil p)))
def c1876 : List Lit := [(388, false)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c1865, c986] c1876 (by decide) p (sat_cons (step1865 p h) (sat_cons (step986 p h) (sat_nil p)))
def c1877 : List Lit := [(370, false)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c1866, c957] c1877 (by decide) p (sat_cons (step1866 p h) (sat_cons (step957 p h) (sat_nil p)))
def c1878 : List Lit := [(364, false)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c1866, c960] c1878 (by decide) p (sat_cons (step1866 p h) (sat_cons (step960 p h) (sat_nil p)))
def c1879 : List Lit := [(340, false)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c1867, c928] c1879 (by decide) p (sat_cons (step1867 p h) (sat_cons (step928 p h) (sat_nil p)))
def c1880 : List Lit := [(308, false)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c1869, c892] c1880 (by decide) p (sat_cons (step1869 p h) (sat_cons (step892 p h) (sat_nil p)))
def c1881 : List Lit := [(294, false)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c1870, c880] c1881 (by decide) p (sat_cons (step1870 p h) (sat_cons (step880 p h) (sat_nil p)))
def c1882 : List Lit := [(288, false)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c1870, c883] c1882 (by decide) p (sat_cons (step1870 p h) (sat_cons (step883 p h) (sat_nil p)))
def c1883 : List Lit := [(278, false)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c1871, c860] c1883 (by decide) p (sat_cons (step1871 p h) (sat_cons (step860 p h) (sat_nil p)))
def c1884 : List Lit := [(272, false)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c1871, c863] c1884 (by decide) p (sat_cons (step1871 p h) (sat_cons (step863 p h) (sat_nil p)))
def c1885 : List Lit := [(264, false)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c1872, c845] c1885 (by decide) p (sat_cons (step1872 p h) (sat_cons (step845 p h) (sat_nil p)))
def c1886 : List Lit := [(258, false)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c1872, c848] c1886 (by decide) p (sat_cons (step1872 p h) (sat_cons (step848 p h) (sat_nil p)))
def c1887 : List Lit := [(384, false)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c1876, c984] c1887 (by decide) p (sat_cons (step1876 p h) (sat_cons (step984 p h) (sat_nil p)))
def c1888 : List Lit := [(366, false)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c1877, c955] c1888 (by decide) p (sat_cons (step1877 p h) (sat_cons (step955 p h) (sat_nil p)))
def c1889 : List Lit := [(336, false)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c1879, c926] c1889 (by decide) p (sat_cons (step1879 p h) (sat_cons (step926 p h) (sat_nil p)))
def c1890 : List Lit := [(286, false)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c1882, c873] c1890 (by decide) p (sat_cons (step1882 p h) (sat_cons (step873 p h) (sat_nil p)))
def c1891 : List Lit := [(276, false)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c1883, c858] c1891 (by decide) p (sat_cons (step1883 p h) (sat_cons (step858 p h) (sat_nil p)))
def c1892 : List Lit := [(270, false)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c1884, c853] c1892 (by decide) p (sat_cons (step1884 p h) (sat_cons (step853 p h) (sat_nil p)))
def c1893 : List Lit := [(128, true), (129, true), (132, true), (134, true), (137, true), (138, true), (141, true), (142, true), (145, true), (146, true), (148, true), (150, true), (152, true), (155, true), (157, true), (160, true), (161, true), (163, true), (168, true), (169, true), (170, true), (171, true), (172, true), (174, true), (176, true), (180, true), (184, true), (185, true), (187, true), (188, true), (189, true), (190, true), (192, true), (194, true), (195, true), (197, true), (201, true), (203, true), (205, true), (206, true), (210, true), (211, true), (215, true), (217, true), (218, true), (220, true), (223, true), (228, true), (230, true), (232, true), (233, true), (235, true), (236, true), (238, true), (240, true), (243, true), (245, true), (247, true), (249, true), (251, true), (253, true)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.TreeRup.prove_clause [c770, c771, c772, c773, c774, c775, c776, c777, c778, c779, c780, c781, c782, c783, c784, c785, c786, c787, c788, c789, c790, c791, c792, c793, c794, c795, c796, c797, c798, c799, c800, c801, c802, c803, c804, c805, c806, c807, c808, c809, c810, c811, c812, c813, c814, c815, c816, c817, c818, c819, c820, c821, c822, c823, c824, c825, c826, c827, c828, c829, c830, c831, c832, c833, c834, c1097] c1893 (by decide) p (sat_cons (step770 p h) (sat_cons (step771 p h) (sat_cons (step772 p h) (sat_cons (step773 p h) (sat_cons (step774 p h) (sat_cons (step775 p h) (sat_cons (step776 p h) (sat_cons (step777 p h) (sat_cons (step778 p h) (sat_cons (step779 p h) (sat_cons (step780 p h) (sat_cons (step781 p h) (sat_cons (step782 p h) (sat_cons (step783 p h) (sat_cons (step784 p h) (sat_cons (step785 p h) (sat_cons (step786 p h) (sat_cons (step787 p h) (sat_cons (step788 p h) (sat_cons (step789 p h) (sat_cons (step790 p h) (sat_cons (step791 p h) (sat_cons (step792 p h) (sat_cons (step793 p h) (sat_cons (step794 p h) (sat_cons (step795 p h) (sat_cons (step796 p h) (sat_cons (step797 p h) (sat_cons (step798 p h) (sat_cons (step799 p h) (sat_cons (step800 p h) (sat_cons (step801 p h) (sat_cons (step802 p h) (sat_cons (step803 p h) (sat_cons (step804 p h) (sat_cons (step805 p h) (sat_cons (step806 p h) (sat_cons (step807 p h) (sat_cons (step808 p h) (sat_cons (step809 p h) (sat_cons (step810 p h) (sat_cons (step811 p h) (sat_cons (step812 p h) (sat_cons (step813 p h) (sat_cons (step814 p h) (sat_cons (step815 p h) (sat_cons (step816 p h) (sat_cons (step817 p h) (sat_cons (step818 p h) (sat_cons (step819 p h) (sat_cons (step820 p h) (sat_cons (step821 p h) (sat_cons (step822 p h) (sat_cons (step823 p h) (sat_cons (step824 p h) (sat_cons (step825 p h) (sat_cons (step826 p h) (sat_cons (step827 p h) (sat_cons (step828 p h) (sat_cons (step829 p h) (sat_cons (step830 p h) (sat_cons (step831 p h) (sat_cons (step832 p h) (sat_cons (step833 p h) (sat_cons (step834 p h) (sat_cons (step1097 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1894 : List Lit := [(3, true), (1530, true)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c1845, c1741] c1894 (by decide) p (sat_cons (step1845 p h) (sat_cons (step1741 p h) (sat_nil p)))
def c1895 : List Lit := [(75, false), (74, true), (99, false)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c807, c503, c502, c1834] c1895 (by decide) p (sat_cons (step807 p h) (sat_cons (step503 p h) (sat_cons (step502 p h) (sat_cons (step1834 p h) (sat_nil p)))))
def c1896 : List Lit := [(51, false), (36, true), (38, false), (40, false), (46, false)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c789, c278, c298, c247] c1896 (by decide) p (sat_cons (step789 p h) (sat_cons (step278 p h) (sat_cons (step298 p h) (sat_cons (step247 p h) (sat_nil p)))))
def c1897 : List Lit := [(18, true), (13, false), (46, false)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c776, c87, c88, c1808] c1897 (by decide) p (sat_cons (step776 p h) (sat_cons (step87 p h) (sat_cons (step88 p h) (sat_cons (step1808 p h) (sat_nil p)))))
def c1898 : List Lit := [(97, false), (121, false), (101, true)]
theorem step1898 (p : Nat → Bool) (h : Constraints p) : clause p c1898 = true :=
  Snake9.LocalRup.prove_clause [c818, c614, c615, c1842] c1898 (by decide) p (sat_cons (step818 p h) (sat_cons (step614 p h) (sat_cons (step615 p h) (sat_cons (step1842 p h) (sat_nil p)))))
def c1899 : List Lit := [(74, false), (87, true), (90, true), (99, true), (77, true)]
theorem step1899 (p : Nat → Bool) (h : Constraints p) : clause p c1899 = true :=
  Snake9.LocalRup.prove_clause [c807, c1864, c496, c498, c501, c988, c506, c989, c990, c998, c993] c1899 (by decide) p (sat_cons (step807 p h) (sat_cons (step1864 p h) (sat_cons (step496 p h) (sat_cons (step498 p h) (sat_cons (step501 p h) (sat_cons (step988 p h) (sat_cons (step506 p h) (sat_cons (step989 p h) (sat_cons (step990 p h) (sat_cons (step998 p h) (sat_cons (step993 p h) (sat_nil p))))))))))))
def c1900 : List Lit := [(1021, true), (84, true), (215, true), (87, true), (90, false), (101, true)]
theorem step1900 (p : Nat → Bool) (h : Constraints p) : clause p c1900 = true :=
  Snake9.LocalRup.prove_clause [c819, c1491, c1501, c1499, c1492, c1493, c599, c582, c581, c616, c1840] c1900 (by decide) p (sat_cons (step819 p h) (sat_cons (step1491 p h) (sat_cons (step1501 p h) (sat_cons (step1499 p h) (sat_cons (step1492 p h) (sat_cons (step1493 p h) (sat_cons (step599 p h) (sat_cons (step582 p h) (sat_cons (step581 p h) (sat_cons (step616 p h) (sat_cons (step1840 p h) (sat_nil p))))))))))))
def c1901 : List Lit := [(1001, true), (195, true)]
theorem step1901 (p : Nat → Bool) (h : Constraints p) : clause p c1901 = true :=
  Snake9.LocalRup.prove_clause [c1457, c1461, c1449, c1451, c1438, c1440, c1447, c1443, c1444, c1436, c492, c460, c471] c1901 (by decide) p (sat_cons (step1457 p h) (sat_cons (step1461 p h) (sat_cons (step1449 p h) (sat_cons (step1451 p h) (sat_cons (step1438 p h) (sat_cons (step1440 p h) (sat_cons (step1447 p h) (sat_cons (step1443 p h) (sat_cons (step1444 p h) (sat_cons (step1436 p h) (sat_cons (step492 p h) (sat_cons (step460 p h) (sat_cons (step471 p h) (sat_nil p))))))))))))))
def c1902 : List Lit := [(1047, true), (220, true), (80, true), (90, false)]
theorem step1902 (p : Nat → Bool) (h : Constraints p) : clause p c1902 = true :=
  Snake9.LocalRup.prove_clause [c1562, c1563, c633, c606] c1902 (by decide) p (sat_cons (step1562 p h) (sat_cons (step1563 p h) (sat_cons (step633 p h) (sat_cons (step606 p h) (sat_nil p)))))
def c1903 : List Lit := [(74, false), (201, true), (90, false)]
theorem step1903 (p : Nat → Bool) (h : Constraints p) : clause p c1903 = true :=
  Snake9.LocalRup.prove_clause [c499, c498, c1833] c1903 (by decide) p (sat_cons (step499 p h) (sat_cons (step498 p h) (sat_cons (step1833 p h) (sat_nil p))))
def c1904 : List Lit := [(58, false), (7, false), (41, false), (377, true), (60, false), (59, false)]
theorem step1904 (p : Nat → Bool) (h : Constraints p) : clause p c1904 = true :=
  Snake9.LocalRup.prove_clause [c780, c770, c972, c902, c866, c844, c841, c840, c900, c897, c879, c877, c874, c970, c965, c961, c958, c944, c943, c393, c392, c149, c401, c147, c63, c14, c30] c1904 (by decide) p (sat_cons (step780 p h) (sat_cons (step770 p h) (sat_cons (step972 p h) (sat_cons (step902 p h) (sat_cons (step866 p h) (sat_cons (step844 p h) (sat_cons (step841 p h) (sat_cons (step840 p h) (sat_cons (step900 p h) (sat_cons (step897 p h) (sat_cons (step879 p h) (sat_cons (step877 p h) (sat_cons (step874 p h) (sat_cons (step970 p h) (sat_cons (step965 p h) (sat_cons (step961 p h) (sat_cons (step958 p h) (sat_cons (step944 p h) (sat_cons (step943 p h) (sat_cons (step393 p h) (sat_cons (step392 p h) (sat_cons (step149 p h) (sat_cons (step401 p h) (sat_cons (step147 p h) (sat_cons (step63 p h) (sat_cons (step14 p h) (sat_cons (step30 p h) (sat_nil p))))))))))))))))))))))))))))
def c1905 : List Lit := [(5, false), (7, false), (40, true), (41, false), (132, true)]
theorem step1905 (p : Nat → Bool) (h : Constraints p) : clause p c1905 = true :=
  Snake9.LocalRup.prove_clause [c21, c40] c1905 (by decide) p (sat_cons (step21 p h) (sat_cons (step40 p h) (sat_nil p)))
def c1906 : List Lit := [(96, false), (1080, true), (101, false), (223, true), (85, true), (99, true), (126, false)]
theorem step1906 (p : Nat → Bool) (h : Constraints p) : clause p c1906 = true :=
  Snake9.LocalRup.prove_clause [c612, c611, c613, c738, c1626] c1906 (by decide) p (sat_cons (step612 p h) (sat_cons (step611 p h) (sat_cons (step613 p h) (sat_cons (step738 p h) (sat_cons (step1626 p h) (sat_nil p))))))
def c1907 : List Lit := [(1048, false), (1066, true), (230, true), (88, false), (1055, false)]
theorem step1907 (p : Nat → Bool) (h : Constraints p) : clause p c1907 = true :=
  Snake9.LocalRup.prove_clause [c1584, c1604, c1573, c1574, c1600, c1565, c1585, c658, c681, c1580] c1907 (by decide) p (sat_cons (step1584 p h) (sat_cons (step1604 p h) (sat_cons (step1573 p h) (sat_cons (step1574 p h) (sat_cons (step1600 p h) (sat_cons (step1565 p h) (sat_cons (step1585 p h) (sat_cons (step658 p h) (sat_cons (step681 p h) (sat_cons (step1580 p h) (sat_nil p)))))))))))
end B112E256
