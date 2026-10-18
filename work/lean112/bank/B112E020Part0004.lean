import B112E020Part0003
namespace B112E020
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1868 : List Lit := [(70, true), (62, true), (64, true), (65, false)]
theorem step1868 (p : Nat → Bool) (h : Constraints p) : clause p c1868 = true :=
  Snake9.LocalRup.prove_clause [c799, c380] c1868 (by decide) p (sat_cons (step799 p h) (sat_cons (step380 p h) (sat_nil p)))
def c1869 : List Lit := [(70, true), (62, true), (63, true), (65, false)]
theorem step1869 (p : Nat → Bool) (h : Constraints p) : clause p c1869 = true :=
  Snake9.LocalRup.prove_clause [c799, c381] c1869 (by decide) p (sat_cons (step799 p h) (sat_cons (step381 p h) (sat_nil p)))
def c1870 : List Lit := [(63, true), (64, true), (65, false), (62, true)]
theorem step1870 (p : Nat → Bool) (h : Constraints p) : clause p c1870 = true :=
  Snake9.LocalRup.prove_clause [c799, c382] c1870 (by decide) p (sat_cons (step799 p h) (sat_cons (step382 p h) (sat_nil p)))
def c1871 : List Lit := [(55, true), (119, true), (67, true), (66, false)]
theorem step1871 (p : Nat → Bool) (h : Constraints p) : clause p c1871 = true :=
  Snake9.LocalRup.prove_clause [c800, c384] c1871 (by decide) p (sat_cons (step800 p h) (sat_cons (step384 p h) (sat_nil p)))
def c1872 : List Lit := [(119, true), (66, false), (67, true), (46, true)]
theorem step1872 (p : Nat → Bool) (h : Constraints p) : clause p c1872 = true :=
  Snake9.LocalRup.prove_clause [c800, c385] c1872 (by decide) p (sat_cons (step800 p h) (sat_cons (step385 p h) (sat_nil p)))
def c1873 : List Lit := [(119, true), (55, true), (46, true), (66, false)]
theorem step1873 (p : Nat → Bool) (h : Constraints p) : clause p c1873 = true :=
  Snake9.LocalRup.prove_clause [c800, c386] c1873 (by decide) p (sat_cons (step800 p h) (sat_cons (step386 p h) (sat_nil p)))
def c1874 : List Lit := [(55, true), (66, false), (46, true), (67, true)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c800, c387] c1874 (by decide) p (sat_cons (step800 p h) (sat_cons (step387 p h) (sat_nil p)))
def c1875 : List Lit := [(62, true), (70, true), (120, true), (67, true), (68, false)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c801, c413] c1875 (by decide) p (sat_cons (step801 p h) (sat_cons (step413 p h) (sat_nil p)))
def c1876 : List Lit := [(120, true), (70, true), (67, true), (57, true), (68, false)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c801, c414] c1876 (by decide) p (sat_cons (step801 p h) (sat_cons (step414 p h) (sat_nil p)))
def c1877 : List Lit := [(120, true), (62, true), (57, true), (68, false), (67, true)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c801, c415] c1877 (by decide) p (sat_cons (step801 p h) (sat_cons (step415 p h) (sat_nil p)))
def c1878 : List Lit := [(70, true), (62, true), (68, false), (57, true), (67, true)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c801, c416] c1878 (by decide) p (sat_cons (step801 p h) (sat_cons (step416 p h) (sat_nil p)))
def c1879 : List Lit := [(122, true), (70, true), (69, false), (67, true)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c802, c419] c1879 (by decide) p (sat_cons (step802 p h) (sat_cons (step419 p h) (sat_nil p)))
def c1880 : List Lit := [(122, true), (70, true), (63, true), (69, false)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c802, c420] c1880 (by decide) p (sat_cons (step802 p h) (sat_cons (step420 p h) (sat_nil p)))
def c1881 : List Lit := [(122, true), (63, true), (69, false), (67, true)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c802, c421] c1881 (by decide) p (sat_cons (step802 p h) (sat_cons (step421 p h) (sat_nil p)))
def c1882 : List Lit := [(70, true), (63, true), (67, true), (69, false)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c802, c422] c1882 (by decide) p (sat_cons (step802 p h) (sat_cons (step422 p h) (sat_nil p)))
def c1883 : List Lit := [(73, false), (77, true)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c803, c433] c1883 (by decide) p (sat_cons (step803 p h) (sat_cons (step433 p h) (sat_nil p)))
def c1884 : List Lit := [(73, false), (72, true)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c803, c434] c1884 (by decide) p (sat_cons (step803 p h) (sat_cons (step434 p h) (sat_nil p)))
def c1885 : List Lit := [(71, true), (108, true), (75, false), (74, true)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c804, c438] c1885 (by decide) p (sat_cons (step804 p h) (sat_cons (step438 p h) (sat_nil p)))
def c1886 : List Lit := [(19, true), (108, true), (74, true), (75, false)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c804, c439] c1886 (by decide) p (sat_cons (step804 p h) (sat_cons (step439 p h) (sat_nil p)))
def c1887 : List Lit := [(71, true), (19, true), (108, true), (75, false)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c804, c440] c1887 (by decide) p (sat_cons (step804 p h) (sat_cons (step440 p h) (sat_nil p)))
def c1888 : List Lit := [(77, true), (76, false), (82, true)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c805, c442] c1888 (by decide) p (sat_cons (step805 p h) (sat_cons (step442 p h) (sat_nil p)))
def c1889 : List Lit := [(82, true), (74, true), (76, false)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c805, c443] c1889 (by decide) p (sat_cons (step805 p h) (sat_cons (step443 p h) (sat_nil p)))
def c1890 : List Lit := [(77, true), (76, false), (74, true)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c805, c444] c1890 (by decide) p (sat_cons (step805 p h) (sat_cons (step444 p h) (sat_nil p)))
def c1891 : List Lit := [(79, true), (82, true), (115, true), (78, false)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c806, c449] c1891 (by decide) p (sat_cons (step806 p h) (sat_cons (step449 p h) (sat_nil p)))
def c1892 : List Lit := [(26, true), (82, true), (78, false), (115, true)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c806, c450] c1892 (by decide) p (sat_cons (step806 p h) (sat_cons (step450 p h) (sat_nil p)))
def c1893 : List Lit := [(79, true), (26, true), (78, false), (115, true)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.LocalRup.prove_clause [c806, c451] c1893 (by decide) p (sat_cons (step806 p h) (sat_cons (step451 p h) (sat_nil p)))
def c1894 : List Lit := [(79, true), (26, true), (78, false), (82, true)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c806, c452] c1894 (by decide) p (sat_cons (step806 p h) (sat_cons (step452 p h) (sat_nil p)))
def c1895 : List Lit := [(85, true), (120, true), (83, false), (82, true)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c807, c468] c1895 (by decide) p (sat_cons (step807 p h) (sat_cons (step468 p h) (sat_nil p)))
def c1896 : List Lit := [(79, true), (85, true), (83, false), (120, true)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c807, c469] c1896 (by decide) p (sat_cons (step807 p h) (sat_cons (step469 p h) (sat_nil p)))
def c1897 : List Lit := [(120, true), (79, true), (82, true), (83, false)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c807, c470] c1897 (by decide) p (sat_cons (step807 p h) (sat_cons (step470 p h) (sat_nil p)))
def c1898 : List Lit := [(85, true), (79, true), (82, true), (83, false)]
theorem step1898 (p : Nat → Bool) (h : Constraints p) : clause p c1898 = true :=
  Snake9.LocalRup.prove_clause [c807, c471] c1898 (by decide) p (sat_cons (step807 p h) (sat_cons (step471 p h) (sat_nil p)))
def c1899 : List Lit := [(85, true), (122, true), (84, false)]
theorem step1899 (p : Nat → Bool) (h : Constraints p) : clause p c1899 = true :=
  Snake9.LocalRup.prove_clause [c808, c473] c1899 (by decide) p (sat_cons (step808 p h) (sat_cons (step473 p h) (sat_nil p)))
def c1900 : List Lit := [(122, true), (84, false), (81, true)]
theorem step1900 (p : Nat → Bool) (h : Constraints p) : clause p c1900 = true :=
  Snake9.LocalRup.prove_clause [c808, c474] c1900 (by decide) p (sat_cons (step808 p h) (sat_cons (step474 p h) (sat_nil p)))
def c1901 : List Lit := [(85, true), (84, false), (81, true)]
theorem step1901 (p : Nat → Bool) (h : Constraints p) : clause p c1901 = true :=
  Snake9.LocalRup.prove_clause [c808, c475] c1901 (by decide) p (sat_cons (step808 p h) (sat_cons (step475 p h) (sat_nil p)))
def c1902 : List Lit := [(93, true), (89, true), (88, false)]
theorem step1902 (p : Nat → Bool) (h : Constraints p) : clause p c1902 = true :=
  Snake9.LocalRup.prove_clause [c809, c486] c1902 (by decide) p (sat_cons (step809 p h) (sat_cons (step486 p h) (sat_nil p)))
def c1903 : List Lit := [(87, true), (89, true), (88, false)]
theorem step1903 (p : Nat → Bool) (h : Constraints p) : clause p c1903 = true :=
  Snake9.LocalRup.prove_clause [c809, c487] c1903 (by decide) p (sat_cons (step809 p h) (sat_cons (step487 p h) (sat_nil p)))
def c1904 : List Lit := [(90, true), (108, true), (91, false)]
theorem step1904 (p : Nat → Bool) (h : Constraints p) : clause p c1904 = true :=
  Snake9.LocalRup.prove_clause [c810, c491] c1904 (by decide) p (sat_cons (step810 p h) (sat_cons (step491 p h) (sat_nil p)))
def c1905 : List Lit := [(108, true), (91, false), (86, true)]
theorem step1905 (p : Nat → Bool) (h : Constraints p) : clause p c1905 = true :=
  Snake9.LocalRup.prove_clause [c810, c492] c1905 (by decide) p (sat_cons (step810 p h) (sat_cons (step492 p h) (sat_nil p)))
def c1906 : List Lit := [(93, true), (98, true), (92, false)]
theorem step1906 (p : Nat → Bool) (h : Constraints p) : clause p c1906 = true :=
  Snake9.LocalRup.prove_clause [c811, c494] c1906 (by decide) p (sat_cons (step811 p h) (sat_cons (step494 p h) (sat_nil p)))
def c1907 : List Lit := [(98, true), (92, false), (90, true)]
theorem step1907 (p : Nat → Bool) (h : Constraints p) : clause p c1907 = true :=
  Snake9.LocalRup.prove_clause [c811, c495] c1907 (by decide) p (sat_cons (step811 p h) (sat_cons (step495 p h) (sat_nil p)))
def c1908 : List Lit := [(93, true), (92, false), (90, true)]
theorem step1908 (p : Nat → Bool) (h : Constraints p) : clause p c1908 = true :=
  Snake9.LocalRup.prove_clause [c811, c496] c1908 (by decide) p (sat_cons (step811 p h) (sat_cons (step496 p h) (sat_nil p)))
def c1909 : List Lit := [(98, true), (94, false), (115, true)]
theorem step1909 (p : Nat → Bool) (h : Constraints p) : clause p c1909 = true :=
  Snake9.LocalRup.prove_clause [c812, c498] c1909 (by decide) p (sat_cons (step812 p h) (sat_cons (step498 p h) (sat_nil p)))
def c1910 : List Lit := [(95, true), (94, false), (115, true)]
theorem step1910 (p : Nat → Bool) (h : Constraints p) : clause p c1910 = true :=
  Snake9.LocalRup.prove_clause [c812, c499] c1910 (by decide) p (sat_cons (step812 p h) (sat_cons (step499 p h) (sat_nil p)))
def c1911 : List Lit := [(98, true), (95, true), (94, false)]
theorem step1911 (p : Nat → Bool) (h : Constraints p) : clause p c1911 = true :=
  Snake9.LocalRup.prove_clause [c812, c500] c1911 (by decide) p (sat_cons (step812 p h) (sat_cons (step500 p h) (sat_nil p)))
def c1912 : List Lit := [(87, true), (96, false), (97, true), (117, true)]
theorem step1912 (p : Nat → Bool) (h : Constraints p) : clause p c1912 = true :=
  Snake9.LocalRup.prove_clause [c813, c505] c1912 (by decide) p (sat_cons (step813 p h) (sat_cons (step505 p h) (sat_nil p)))
def c1913 : List Lit := [(87, true), (96, false), (117, true), (44, true)]
theorem step1913 (p : Nat → Bool) (h : Constraints p) : clause p c1913 = true :=
  Snake9.LocalRup.prove_clause [c813, c506] c1913 (by decide) p (sat_cons (step813 p h) (sat_cons (step506 p h) (sat_nil p)))
def c1914 : List Lit := [(87, true), (96, false), (97, true), (44, true)]
theorem step1914 (p : Nat → Bool) (h : Constraints p) : clause p c1914 = true :=
  Snake9.LocalRup.prove_clause [c813, c507] c1914 (by decide) p (sat_cons (step813 p h) (sat_cons (step507 p h) (sat_nil p)))
def c1915 : List Lit := [(98, true), (99, false), (120, true), (101, true)]
theorem step1915 (p : Nat → Bool) (h : Constraints p) : clause p c1915 = true :=
  Snake9.LocalRup.prove_clause [c814, c516] c1915 (by decide) p (sat_cons (step814 p h) (sat_cons (step516 p h) (sat_nil p)))
def c1916 : List Lit := [(95, true), (98, true), (99, false), (120, true)]
theorem step1916 (p : Nat → Bool) (h : Constraints p) : clause p c1916 = true :=
  Snake9.LocalRup.prove_clause [c814, c517] c1916 (by decide) p (sat_cons (step814 p h) (sat_cons (step517 p h) (sat_nil p)))
def c1917 : List Lit := [(101, true), (122, true), (100, false)]
theorem step1917 (p : Nat → Bool) (h : Constraints p) : clause p c1917 = true :=
  Snake9.LocalRup.prove_clause [c815, c519] c1917 (by decide) p (sat_cons (step815 p h) (sat_cons (step519 p h) (sat_nil p)))
def c1918 : List Lit := [(97, true), (122, true), (100, false)]
theorem step1918 (p : Nat → Bool) (h : Constraints p) : clause p c1918 = true :=
  Snake9.LocalRup.prove_clause [c815, c520] c1918 (by decide) p (sat_cons (step815 p h) (sat_cons (step520 p h) (sat_nil p)))
def c1919 : List Lit := [(105, true), (104, false), (115, true)]
theorem step1919 (p : Nat → Bool) (h : Constraints p) : clause p c1919 = true :=
  Snake9.LocalRup.prove_clause [c816, c537] c1919 (by decide) p (sat_cons (step816 p h) (sat_cons (step537 p h) (sat_nil p)))
def c1920 : List Lit := [(104, false), (102, true), (115, true)]
theorem step1920 (p : Nat → Bool) (h : Constraints p) : clause p c1920 = true :=
  Snake9.LocalRup.prove_clause [c816, c538] c1920 (by decide) p (sat_cons (step816 p h) (sat_cons (step538 p h) (sat_nil p)))
def c1921 : List Lit := [(105, true), (102, true), (104, false)]
theorem step1921 (p : Nat → Bool) (h : Constraints p) : clause p c1921 = true :=
  Snake9.LocalRup.prove_clause [c816, c539] c1921 (by decide) p (sat_cons (step816 p h) (sat_cons (step539 p h) (sat_nil p)))
def c1922 : List Lit := [(112, true), (105, true), (106, false)]
theorem step1922 (p : Nat → Bool) (h : Constraints p) : clause p c1922 = true :=
  Snake9.LocalRup.prove_clause [c817, c552] c1922 (by decide) p (sat_cons (step817 p h) (sat_cons (step552 p h) (sat_nil p)))
def c1923 : List Lit := [(112, true), (89, true), (106, false)]
theorem step1923 (p : Nat → Bool) (h : Constraints p) : clause p c1923 = true :=
  Snake9.LocalRup.prove_clause [c817, c553] c1923 (by decide) p (sat_cons (step817 p h) (sat_cons (step553 p h) (sat_nil p)))
def c1924 : List Lit := [(89, true), (105, true), (106, false)]
theorem step1924 (p : Nat → Bool) (h : Constraints p) : clause p c1924 = true :=
  Snake9.LocalRup.prove_clause [c817, c554] c1924 (by decide) p (sat_cons (step817 p h) (sat_cons (step554 p h) (sat_nil p)))
def c1925 : List Lit := [(112, true), (108, true), (109, false), (120, true), (105, true)]
theorem step1925 (p : Nat → Bool) (h : Constraints p) : clause p c1925 = true :=
  Snake9.LocalRup.prove_clause [c818, c595] c1925 (by decide) p (sat_cons (step818 p h) (sat_cons (step595 p h) (sat_nil p)))
def c1926 : List Lit := [(108, true), (105, true), (120, true), (57, true), (109, false)]
theorem step1926 (p : Nat → Bool) (h : Constraints p) : clause p c1926 = true :=
  Snake9.LocalRup.prove_clause [c818, c596] c1926 (by decide) p (sat_cons (step818 p h) (sat_cons (step596 p h) (sat_nil p)))
def c1927 : List Lit := [(112, true), (111, false), (110, true), (122, true)]
theorem step1927 (p : Nat → Bool) (h : Constraints p) : clause p c1927 = true :=
  Snake9.LocalRup.prove_clause [c819, c605] c1927 (by decide) p (sat_cons (step819 p h) (sat_cons (step605 p h) (sat_nil p)))
def c1928 : List Lit := [(112, true), (108, true), (111, false), (122, true)]
theorem step1928 (p : Nat → Bool) (h : Constraints p) : clause p c1928 = true :=
  Snake9.LocalRup.prove_clause [c819, c606] c1928 (by decide) p (sat_cons (step819 p h) (sat_cons (step606 p h) (sat_nil p)))
def c1929 : List Lit := [(108, true), (111, false), (122, true), (110, true)]
theorem step1929 (p : Nat → Bool) (h : Constraints p) : clause p c1929 = true :=
  Snake9.LocalRup.prove_clause [c819, c607] c1929 (by decide) p (sat_cons (step819 p h) (sat_cons (step607 p h) (sat_nil p)))
def c1930 : List Lit := [(112, true), (108, true), (111, false), (110, true)]
theorem step1930 (p : Nat → Bool) (h : Constraints p) : clause p c1930 = true :=
  Snake9.LocalRup.prove_clause [c819, c608] c1930 (by decide) p (sat_cons (step819 p h) (sat_cons (step608 p h) (sat_nil p)))
def c1931 : List Lit := [(114, true), (113, false), (119, true), (115, true), (117, true)]
theorem step1931 (p : Nat → Bool) (h : Constraints p) : clause p c1931 = true :=
  Snake9.LocalRup.prove_clause [c820, c616] c1931 (by decide) p (sat_cons (step820 p h) (sat_cons (step616 p h) (sat_nil p)))
end B112E020
