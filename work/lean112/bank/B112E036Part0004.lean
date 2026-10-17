import B112E036Part0003
namespace B112E036
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1901 : List Lit := [(86, true), (71, true), (79, true), (82, false)]
theorem step1901 (p : Nat → Bool) (h : Constraints p) : clause p c1901 = true :=
  Snake9.LocalRup.prove_clause [c807, c395] c1901 (by decide) p (sat_cons (step807 p h) (sat_cons (step395 p h) (sat_nil p)))
def c1902 : List Lit := [(79, true), (86, true), (83, false), (108, true)]
theorem step1902 (p : Nat → Bool) (h : Constraints p) : clause p c1902 = true :=
  Snake9.LocalRup.prove_clause [c808, c396] c1902 (by decide) p (sat_cons (step808 p h) (sat_cons (step396 p h) (sat_nil p)))
def c1903 : List Lit := [(86, true), (15, true), (108, true), (83, false)]
theorem step1903 (p : Nat → Bool) (h : Constraints p) : clause p c1903 = true :=
  Snake9.LocalRup.prove_clause [c808, c397] c1903 (by decide) p (sat_cons (step808 p h) (sat_cons (step397 p h) (sat_nil p)))
def c1904 : List Lit := [(79, true), (86, true), (83, false), (15, true)]
theorem step1904 (p : Nat → Bool) (h : Constraints p) : clause p c1904 = true :=
  Snake9.LocalRup.prove_clause [c808, c398] c1904 (by decide) p (sat_cons (step808 p h) (sat_cons (step398 p h) (sat_nil p)))
def c1905 : List Lit := [(85, true), (86, true), (84, false)]
theorem step1905 (p : Nat → Bool) (h : Constraints p) : clause p c1905 = true :=
  Snake9.LocalRup.prove_clause [c809, c399] c1905 (by decide) p (sat_cons (step809 p h) (sat_cons (step399 p h) (sat_nil p)))
def c1906 : List Lit := [(81, true), (86, true), (84, false)]
theorem step1906 (p : Nat → Bool) (h : Constraints p) : clause p c1906 = true :=
  Snake9.LocalRup.prove_clause [c809, c400] c1906 (by decide) p (sat_cons (step809 p h) (sat_cons (step400 p h) (sat_nil p)))
def c1907 : List Lit := [(85, true), (81, true), (84, false)]
theorem step1907 (p : Nat → Bool) (h : Constraints p) : clause p c1907 = true :=
  Snake9.LocalRup.prove_clause [c809, c401] c1907 (by decide) p (sat_cons (step809 p h) (sat_cons (step401 p h) (sat_nil p)))
def c1908 : List Lit := [(104, true), (94, true), (92, false), (89, true), (91, true)]
theorem step1908 (p : Nat → Bool) (h : Constraints p) : clause p c1908 = true :=
  Snake9.LocalRup.prove_clause [c810, c467] c1908 (by decide) p (sat_cons (step810 p h) (sat_cons (step467 p h) (sat_nil p)))
def c1909 : List Lit := [(104, true), (94, true), (92, false), (91, true), (35, true)]
theorem step1909 (p : Nat → Bool) (h : Constraints p) : clause p c1909 = true :=
  Snake9.LocalRup.prove_clause [c810, c468] c1909 (by decide) p (sat_cons (step810 p h) (sat_cons (step468 p h) (sat_nil p)))
def c1910 : List Lit := [(104, true), (35, true), (92, false), (94, true), (89, true)]
theorem step1910 (p : Nat → Bool) (h : Constraints p) : clause p c1910 = true :=
  Snake9.LocalRup.prove_clause [c810, c469] c1910 (by decide) p (sat_cons (step810 p h) (sat_cons (step469 p h) (sat_nil p)))
def c1911 : List Lit := [(104, true), (35, true), (92, false), (91, true), (89, true)]
theorem step1911 (p : Nat → Bool) (h : Constraints p) : clause p c1911 = true :=
  Snake9.LocalRup.prove_clause [c810, c470] c1911 (by decide) p (sat_cons (step810 p h) (sat_cons (step470 p h) (sat_nil p)))
def c1912 : List Lit := [(35, true), (94, true), (92, false), (89, true), (91, true)]
theorem step1912 (p : Nat → Bool) (h : Constraints p) : clause p c1912 = true :=
  Snake9.LocalRup.prove_clause [c810, c471] c1912 (by decide) p (sat_cons (step810 p h) (sat_cons (step471 p h) (sat_nil p)))
def c1913 : List Lit := [(71, true), (113, true), (90, true), (91, true), (93, false), (99, true), (94, true)]
theorem step1913 (p : Nat → Bool) (h : Constraints p) : clause p c1913 = true :=
  Snake9.LocalRup.prove_clause [c811, c481] c1913 (by decide) p (sat_cons (step811 p h) (sat_cons (step481 p h) (sat_nil p)))
def c1914 : List Lit := [(99, true), (108, true), (97, true), (96, false), (95, true)]
theorem step1914 (p : Nat → Bool) (h : Constraints p) : clause p c1914 = true :=
  Snake9.LocalRup.prove_clause [c812, c539] c1914 (by decide) p (sat_cons (step812 p h) (sat_cons (step539 p h) (sat_nil p)))
def c1915 : List Lit := [(97, true), (90, true), (108, true), (96, false), (99, true)]
theorem step1915 (p : Nat → Bool) (h : Constraints p) : clause p c1915 = true :=
  Snake9.LocalRup.prove_clause [c812, c540] c1915 (by decide) p (sat_cons (step812 p h) (sat_cons (step540 p h) (sat_nil p)))
def c1916 : List Lit := [(90, true), (96, false), (108, true), (99, true), (95, true)]
theorem step1916 (p : Nat → Bool) (h : Constraints p) : clause p c1916 = true :=
  Snake9.LocalRup.prove_clause [c812, c541] c1916 (by decide) p (sat_cons (step812 p h) (sat_cons (step541 p h) (sat_nil p)))
def c1917 : List Lit := [(90, true), (96, false), (95, true), (108, true), (97, true)]
theorem step1917 (p : Nat → Bool) (h : Constraints p) : clause p c1917 = true :=
  Snake9.LocalRup.prove_clause [c812, c542] c1917 (by decide) p (sat_cons (step812 p h) (sat_cons (step542 p h) (sat_nil p)))
def c1918 : List Lit := [(90, true), (97, true), (95, true), (99, true), (96, false)]
theorem step1918 (p : Nat → Bool) (h : Constraints p) : clause p c1918 = true :=
  Snake9.LocalRup.prove_clause [c812, c543] c1918 (by decide) p (sat_cons (step812 p h) (sat_cons (step543 p h) (sat_nil p)))
def c1919 : List Lit := [(99, true), (98, false), (95, true)]
theorem step1919 (p : Nat → Bool) (h : Constraints p) : clause p c1919 = true :=
  Snake9.LocalRup.prove_clause [c813, c565] c1919 (by decide) p (sat_cons (step813 p h) (sat_cons (step565 p h) (sat_nil p)))
def c1920 : List Lit := [(99, true), (98, false), (91, true)]
theorem step1920 (p : Nat → Bool) (h : Constraints p) : clause p c1920 = true :=
  Snake9.LocalRup.prove_clause [c813, c566] c1920 (by decide) p (sat_cons (step813 p h) (sat_cons (step566 p h) (sat_nil p)))
def c1921 : List Lit := [(98, false), (95, true), (91, true)]
theorem step1921 (p : Nat → Bool) (h : Constraints p) : clause p c1921 = true :=
  Snake9.LocalRup.prove_clause [c813, c567] c1921 (by decide) p (sat_cons (step813 p h) (sat_cons (step567 p h) (sat_nil p)))
def c1922 : List Lit := [(123, true), (103, false), (104, true), (91, true)]
theorem step1922 (p : Nat → Bool) (h : Constraints p) : clause p c1922 = true :=
  Snake9.LocalRup.prove_clause [c814, c629] c1922 (by decide) p (sat_cons (step814 p h) (sat_cons (step629 p h) (sat_nil p)))
def c1923 : List Lit := [(103, false), (81, true), (104, true), (123, true)]
theorem step1923 (p : Nat → Bool) (h : Constraints p) : clause p c1923 = true :=
  Snake9.LocalRup.prove_clause [c814, c630] c1923 (by decide) p (sat_cons (step814 p h) (sat_cons (step630 p h) (sat_nil p)))
def c1924 : List Lit := [(81, true), (123, true), (91, true), (103, false)]
theorem step1924 (p : Nat → Bool) (h : Constraints p) : clause p c1924 = true :=
  Snake9.LocalRup.prove_clause [c814, c631] c1924 (by decide) p (sat_cons (step814 p h) (sat_cons (step631 p h) (sat_nil p)))
def c1925 : List Lit := [(81, true), (103, false), (91, true), (104, true)]
theorem step1925 (p : Nat → Bool) (h : Constraints p) : clause p c1925 = true :=
  Snake9.LocalRup.prove_clause [c814, c632] c1925 (by decide) p (sat_cons (step814 p h) (sat_cons (step632 p h) (sat_nil p)))
def c1926 : List Lit := [(105, false), (110, true), (102, true), (104, true)]
theorem step1926 (p : Nat → Bool) (h : Constraints p) : clause p c1926 = true :=
  Snake9.LocalRup.prove_clause [c815, c640] c1926 (by decide) p (sat_cons (step815 p h) (sat_cons (step640 p h) (sat_nil p)))
def c1927 : List Lit := [(110, true), (105, false), (104, true), (94, true)]
theorem step1927 (p : Nat → Bool) (h : Constraints p) : clause p c1927 = true :=
  Snake9.LocalRup.prove_clause [c815, c641] c1927 (by decide) p (sat_cons (step815 p h) (sat_cons (step641 p h) (sat_nil p)))
def c1928 : List Lit := [(110, true), (94, true), (105, false), (102, true)]
theorem step1928 (p : Nat → Bool) (h : Constraints p) : clause p c1928 = true :=
  Snake9.LocalRup.prove_clause [c815, c642] c1928 (by decide) p (sat_cons (step815 p h) (sat_cons (step642 p h) (sat_nil p)))
def c1929 : List Lit := [(94, true), (104, true), (105, false), (102, true)]
theorem step1929 (p : Nat → Bool) (h : Constraints p) : clause p c1929 = true :=
  Snake9.LocalRup.prove_clause [c815, c643] c1929 (by decide) p (sat_cons (step815 p h) (sat_cons (step643 p h) (sat_nil p)))
def c1930 : List Lit := [(108, true), (106, false), (95, true), (107, true)]
theorem step1930 (p : Nat → Bool) (h : Constraints p) : clause p c1930 = true :=
  Snake9.LocalRup.prove_clause [c816, c648] c1930 (by decide) p (sat_cons (step816 p h) (sat_cons (step648 p h) (sat_nil p)))
def c1931 : List Lit := [(46, true), (107, true), (108, true), (106, false)]
theorem step1931 (p : Nat → Bool) (h : Constraints p) : clause p c1931 = true :=
  Snake9.LocalRup.prove_clause [c816, c649] c1931 (by decide) p (sat_cons (step816 p h) (sat_cons (step649 p h) (sat_nil p)))
def c1932 : List Lit := [(46, true), (108, true), (95, true), (106, false)]
theorem step1932 (p : Nat → Bool) (h : Constraints p) : clause p c1932 = true :=
  Snake9.LocalRup.prove_clause [c816, c650] c1932 (by decide) p (sat_cons (step816 p h) (sat_cons (step650 p h) (sat_nil p)))
def c1933 : List Lit := [(46, true), (107, true), (106, false), (95, true)]
theorem step1933 (p : Nat → Bool) (h : Constraints p) : clause p c1933 = true :=
  Snake9.LocalRup.prove_clause [c816, c651] c1933 (by decide) p (sat_cons (step816 p h) (sat_cons (step651 p h) (sat_nil p)))
def c1934 : List Lit := [(108, true), (110, true), (102, true), (109, false), (107, true)]
theorem step1934 (p : Nat → Bool) (h : Constraints p) : clause p c1934 = true :=
  Snake9.LocalRup.prove_clause [c817, c670] c1934 (by decide) p (sat_cons (step817 p h) (sat_cons (step670 p h) (sat_nil p)))
def c1935 : List Lit := [(108, true), (110, true), (97, true), (109, false), (107, true)]
theorem step1935 (p : Nat → Bool) (h : Constraints p) : clause p c1935 = true :=
  Snake9.LocalRup.prove_clause [c817, c671] c1935 (by decide) p (sat_cons (step817 p h) (sat_cons (step671 p h) (sat_nil p)))
def c1936 : List Lit := [(108, true), (110, true), (102, true), (97, true), (109, false)]
theorem step1936 (p : Nat → Bool) (h : Constraints p) : clause p c1936 = true :=
  Snake9.LocalRup.prove_clause [c817, c672] c1936 (by decide) p (sat_cons (step817 p h) (sat_cons (step672 p h) (sat_nil p)))
def c1937 : List Lit := [(110, true), (107, true), (102, true), (109, false), (97, true)]
theorem step1937 (p : Nat → Bool) (h : Constraints p) : clause p c1937 = true :=
  Snake9.LocalRup.prove_clause [c817, c673] c1937 (by decide) p (sat_cons (step817 p h) (sat_cons (step673 p h) (sat_nil p)))
def c1938 : List Lit := [(108, true), (107, true), (102, true), (97, true), (109, false)]
theorem step1938 (p : Nat → Bool) (h : Constraints p) : clause p c1938 = true :=
  Snake9.LocalRup.prove_clause [c817, c674] c1938 (by decide) p (sat_cons (step817 p h) (sat_cons (step674 p h) (sat_nil p)))
def c1939 : List Lit := [(116, true), (120, true), (89, true), (112, false)]
theorem step1939 (p : Nat → Bool) (h : Constraints p) : clause p c1939 = true :=
  Snake9.LocalRup.prove_clause [c818, c688] c1939 (by decide) p (sat_cons (step818 p h) (sat_cons (step688 p h) (sat_nil p)))
def c1940 : List Lit := [(120, true), (112, false), (89, true), (111, true)]
theorem step1940 (p : Nat → Bool) (h : Constraints p) : clause p c1940 = true :=
  Snake9.LocalRup.prove_clause [c818, c689] c1940 (by decide) p (sat_cons (step818 p h) (sat_cons (step689 p h) (sat_nil p)))
def c1941 : List Lit := [(116, true), (112, false), (89, true), (111, true)]
theorem step1941 (p : Nat → Bool) (h : Constraints p) : clause p c1941 = true :=
  Snake9.LocalRup.prove_clause [c818, c690] c1941 (by decide) p (sat_cons (step818 p h) (sat_cons (step690 p h) (sat_nil p)))
def c1942 : List Lit := [(113, true), (119, true), (114, false)]
theorem step1942 (p : Nat → Bool) (h : Constraints p) : clause p c1942 = true :=
  Snake9.LocalRup.prove_clause [c819, c697] c1942 (by decide) p (sat_cons (step819 p h) (sat_cons (step697 p h) (sat_nil p)))
def c1943 : List Lit := [(119, true), (94, true), (114, false)]
theorem step1943 (p : Nat → Bool) (h : Constraints p) : clause p c1943 = true :=
  Snake9.LocalRup.prove_clause [c819, c698] c1943 (by decide) p (sat_cons (step819 p h) (sat_cons (step698 p h) (sat_nil p)))
def c1944 : List Lit := [(113, true), (94, true), (114, false)]
theorem step1944 (p : Nat → Bool) (h : Constraints p) : clause p c1944 = true :=
  Snake9.LocalRup.prove_clause [c819, c699] c1944 (by decide) p (sat_cons (step819 p h) (sat_cons (step699 p h) (sat_nil p)))
def c1945 : List Lit := [(116, true), (111, true), (115, false)]
theorem step1945 (p : Nat → Bool) (h : Constraints p) : clause p c1945 = true :=
  Snake9.LocalRup.prove_clause [c820, c701] c1945 (by decide) p (sat_cons (step820 p h) (sat_cons (step701 p h) (sat_nil p)))
def c1946 : List Lit := [(116, true), (115, false), (95, true)]
theorem step1946 (p : Nat → Bool) (h : Constraints p) : clause p c1946 = true :=
  Snake9.LocalRup.prove_clause [c820, c702] c1946 (by decide) p (sat_cons (step820 p h) (sat_cons (step702 p h) (sat_nil p)))
def c1947 : List Lit := [(111, true), (115, false), (95, true)]
theorem step1947 (p : Nat → Bool) (h : Constraints p) : clause p c1947 = true :=
  Snake9.LocalRup.prove_clause [c820, c703] c1947 (by decide) p (sat_cons (step820 p h) (sat_cons (step703 p h) (sat_nil p)))
def c1948 : List Lit := [(119, true), (116, true), (97, true), (117, false)]
theorem step1948 (p : Nat → Bool) (h : Constraints p) : clause p c1948 = true :=
  Snake9.LocalRup.prove_clause [c821, c720] c1948 (by decide) p (sat_cons (step821 p h) (sat_cons (step720 p h) (sat_nil p)))
def c1949 : List Lit := [(119, true), (116, true), (58, true), (117, false)]
theorem step1949 (p : Nat → Bool) (h : Constraints p) : clause p c1949 = true :=
  Snake9.LocalRup.prove_clause [c821, c721] c1949 (by decide) p (sat_cons (step821 p h) (sat_cons (step721 p h) (sat_nil p)))
def c1950 : List Lit := [(119, true), (58, true), (117, false), (97, true)]
theorem step1950 (p : Nat → Bool) (h : Constraints p) : clause p c1950 = true :=
  Snake9.LocalRup.prove_clause [c821, c722] c1950 (by decide) p (sat_cons (step821 p h) (sat_cons (step722 p h) (sat_nil p)))
def c1951 : List Lit := [(116, true), (97, true), (58, true), (117, false)]
theorem step1951 (p : Nat → Bool) (h : Constraints p) : clause p c1951 = true :=
  Snake9.LocalRup.prove_clause [c821, c723] c1951 (by decide) p (sat_cons (step821 p h) (sat_cons (step723 p h) (sat_nil p)))
def c1952 : List Lit := [(127, true), (116, true), (118, false)]
theorem step1952 (p : Nat → Bool) (h : Constraints p) : clause p c1952 = true :=
  Snake9.LocalRup.prove_clause [c822, c725] c1952 (by decide) p (sat_cons (step822 p h) (sat_cons (step725 p h) (sat_nil p)))
def c1953 : List Lit := [(119, true), (116, true), (118, false)]
theorem step1953 (p : Nat → Bool) (h : Constraints p) : clause p c1953 = true :=
  Snake9.LocalRup.prove_clause [c822, c726] c1953 (by decide) p (sat_cons (step822 p h) (sat_cons (step726 p h) (sat_nil p)))
def c1954 : List Lit := [(121, true), (122, false), (120, true)]
theorem step1954 (p : Nat → Bool) (h : Constraints p) : clause p c1954 = true :=
  Snake9.LocalRup.prove_clause [c823, c741] c1954 (by decide) p (sat_cons (step823 p h) (sat_cons (step741 p h) (sat_nil p)))
def c1955 : List Lit := [(121, true), (122, false), (102, true)]
theorem step1955 (p : Nat → Bool) (h : Constraints p) : clause p c1955 = true :=
  Snake9.LocalRup.prove_clause [c823, c742] c1955 (by decide) p (sat_cons (step823 p h) (sat_cons (step742 p h) (sat_nil p)))
def c1956 : List Lit := [(120, true), (122, false), (102, true)]
theorem step1956 (p : Nat → Bool) (h : Constraints p) : clause p c1956 = true :=
  Snake9.LocalRup.prove_clause [c823, c743] c1956 (by decide) p (sat_cons (step823 p h) (sat_cons (step743 p h) (sat_nil p)))
def c1957 : List Lit := [(113, true), (121, true), (128, true), (124, false)]
theorem step1957 (p : Nat → Bool) (h : Constraints p) : clause p c1957 = true :=
  Snake9.LocalRup.prove_clause [c824, c751] c1957 (by decide) p (sat_cons (step824 p h) (sat_cons (step751 p h) (sat_nil p)))
def c1958 : List Lit := [(113, true), (123, true), (121, true), (124, false)]
theorem step1958 (p : Nat → Bool) (h : Constraints p) : clause p c1958 = true :=
  Snake9.LocalRup.prove_clause [c824, c752] c1958 (by decide) p (sat_cons (step824 p h) (sat_cons (step752 p h) (sat_nil p)))
def c1959 : List Lit := [(121, true), (125, false), (108, true), (128, true)]
theorem step1959 (p : Nat → Bool) (h : Constraints p) : clause p c1959 = true :=
  Snake9.LocalRup.prove_clause [c825, c755] c1959 (by decide) p (sat_cons (step825 p h) (sat_cons (step755 p h) (sat_nil p)))
def c1960 : List Lit := [(128, true), (121, true), (66, true), (125, false)]
theorem step1960 (p : Nat → Bool) (h : Constraints p) : clause p c1960 = true :=
  Snake9.LocalRup.prove_clause [c825, c756] c1960 (by decide) p (sat_cons (step825 p h) (sat_cons (step756 p h) (sat_nil p)))
def c1961 : List Lit := [(128, true), (125, false), (66, true), (108, true)]
theorem step1961 (p : Nat → Bool) (h : Constraints p) : clause p c1961 = true :=
  Snake9.LocalRup.prove_clause [c825, c757] c1961 (by decide) p (sat_cons (step825 p h) (sat_cons (step757 p h) (sat_nil p)))
def c1962 : List Lit := [(121, true), (125, false), (66, true), (108, true)]
theorem step1962 (p : Nat → Bool) (h : Constraints p) : clause p c1962 = true :=
  Snake9.LocalRup.prove_clause [c825, c758] c1962 (by decide) p (sat_cons (step825 p h) (sat_cons (step758 p h) (sat_nil p)))
def c1963 : List Lit := [(126, false), (128, true), (127, true)]
theorem step1963 (p : Nat → Bool) (h : Constraints p) : clause p c1963 = true :=
  Snake9.LocalRup.prove_clause [c826, c760] c1963 (by decide) p (sat_cons (step826 p h) (sat_cons (step760 p h) (sat_nil p)))
def c1964 : List Lit := [(123, true), (128, true), (126, false)]
theorem step1964 (p : Nat → Bool) (h : Constraints p) : clause p c1964 = true :=
  Snake9.LocalRup.prove_clause [c826, c761] c1964 (by decide) p (sat_cons (step826 p h) (sat_cons (step761 p h) (sat_nil p)))
end B112E036
