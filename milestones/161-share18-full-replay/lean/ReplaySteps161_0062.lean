import ReplayCheck161_01984
import ReplayCheck161_01988
import ReplayCheck161_01992
import ReplayCheck161_01996
import ReplayCheck161_02000
import ReplayCheck161_02004
import ReplayCheck161_02008
import ReplayCheck161_02012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps62 (τ : Nat → Bool) (h1984 : TreeTrue τ start1984) : TreeTrue τ start2016 := by
  have h1985 : TreeTrue τ start1985 := replay_true τ ok1984 h1984
  have h1986 : TreeTrue τ start1986 := replay_true τ ok1985 h1985
  have h1987 : TreeTrue τ start1987 := replay_true τ ok1986 h1986
  have h1988 : TreeTrue τ start1988 := replay_true τ ok1987 h1987
  have h1989 : TreeTrue τ start1989 := replay_true τ ok1988 h1988
  have h1990 : TreeTrue τ start1990 := replay_true τ ok1989 h1989
  have h1991 : TreeTrue τ start1991 := replay_true τ ok1990 h1990
  have h1992 : TreeTrue τ start1992 := replay_true τ ok1991 h1991
  have h1993 : TreeTrue τ start1993 := replay_true τ ok1992 h1992
  have h1994 : TreeTrue τ start1994 := replay_true τ ok1993 h1993
  have h1995 : TreeTrue τ start1995 := replay_true τ ok1994 h1994
  have h1996 : TreeTrue τ start1996 := replay_true τ ok1995 h1995
  have h1997 : TreeTrue τ start1997 := replay_true τ ok1996 h1996
  have h1998 : TreeTrue τ start1998 := replay_true τ ok1997 h1997
  have h1999 : TreeTrue τ start1999 := replay_true τ ok1998 h1998
  have h2000 : TreeTrue τ start2000 := replay_true τ ok1999 h1999
  have h2001 : TreeTrue τ start2001 := replay_true τ ok2000 h2000
  have h2002 : TreeTrue τ start2002 := replay_true τ ok2001 h2001
  have h2003 : TreeTrue τ start2003 := replay_true τ ok2002 h2002
  have h2004 : TreeTrue τ start2004 := replay_true τ ok2003 h2003
  have h2005 : TreeTrue τ start2005 := replay_true τ ok2004 h2004
  have h2006 : TreeTrue τ start2006 := replay_true τ ok2005 h2005
  have h2007 : TreeTrue τ start2007 := replay_true τ ok2006 h2006
  have h2008 : TreeTrue τ start2008 := replay_true τ ok2007 h2007
  have h2009 : TreeTrue τ start2009 := replay_true τ ok2008 h2008
  have h2010 : TreeTrue τ start2010 := replay_true τ ok2009 h2009
  have h2011 : TreeTrue τ start2011 := replay_true τ ok2010 h2010
  have h2012 : TreeTrue τ start2012 := replay_true τ ok2011 h2011
  have h2013 : TreeTrue τ start2013 := replay_true τ ok2012 h2012
  have h2014 : TreeTrue τ start2014 := replay_true τ ok2013 h2013
  have h2015 : TreeTrue τ start2015 := replay_true τ ok2014 h2014
  have h2016 : TreeTrue τ start2016 := cp_true τ ok2015 h2015
  exact h2016
#print axioms steps62
end Snake9.ReplayFull161
