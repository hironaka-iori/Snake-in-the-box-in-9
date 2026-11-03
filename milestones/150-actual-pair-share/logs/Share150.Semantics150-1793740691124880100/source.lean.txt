import Share150.Structure
import Share150.Shard00
import Share150.Shard01
import Share150.Shard02
import Share150.Shard03
import Share150.Shard04
import Share150.Shard05
import Share150.Shard06
import Share150.Shard07
import Share150.Shard08
import Share150.Shard09
import Share150.Shard10
import Share150.Shard11
import Share150.Shard12
import Share150.Shard13
import Share150.Shard14
import Share150.Shard15
import Share150.Shard16
import Share150.Shard17
import Share150.Shard18
import Share150.Shard19
import Share150.Shard20
import Share150.Shard21
import Share150.Shard22
import Share150.Shard23
import Share150.Shard24
import Share150.Shard25
import Share150.Shard26
import Share150.Shard27
import Share150.Shard28
import Share150.Shard29
import Share150.Shard30
import Share150.Shard31
import Share150.Shard32
import Share150.Shard33
import Share150.Shard34
import Share150.Shard35
import Share150.Shard36
import Share150.Shard37
import Share150.Shard38
import Share150.Shard39
import Share150.Shard40
import Share150.Shard41
import Share150.Shard42
import Share150.Shard43
import Share150.Shard44
import Share150.Shard45
import Share150.Shard46
import Share150.Shard47
import Share150.Shard48
import Share150.Shard49
import Share150.Shard50
import Share150.Shard51
import Share150.Shard52
import Share150.Shard53
import Share150.Shard54
import Share150.Shard55
import Share150.Shard56
import Share150.Shard57
import Share150.Shard58
import Share150.Shard59
import Share150.Shard60
import Share150.Shard61
import Share150.Shard62
import Share150.Shard63
import Share150.Shard64
import Share150.Shard65
import Share150.Shard66
import Share150.Shard67
import Share150.Shard68
import Share150.Shard69
import Share150.Shard70
import Share150.Shard71
import Share150.Shard72
import Share150.Shard73
import Share150.Shard74
import Share150.Shard75
import Share150.Shard76
import Share150.Shard77
import Share150.Shard78
import Share150.Shard79
import Share150.Shard80
import Share150.Shard81
import Share150.Shard82
import Share150.Shard83
import Share150.Shard84
import Share150.Shard85
import Share150.Shard86
import Share150.Shard87
import Share150.Shard88
import Share150.Shard89
import Share150.Shard90
import Share150.Shard91
import Share150.Shard92
import Share150.Shard93
import Share150.Shard94
import Share150.Shard95
import Share150.Shard96
import Share150.Shard97
import Share150.Shard98
import Share150.Shard99
import Share150.Shard100
import Share150.Shard101
import Share150.Shard102
import Share150.Shard103
import Share150.Shard104
import Share150.Shard105
import Share150.Shard106
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.LocalWindow.ShareWindow150
open Snake9.LocalWindow.Tags
theorem interpreted_core150 (S E : Nat → Bool)
    (ax : AxiomsS S E window (centresOf window bounds) resolution cap) :
    cnfTrue (tauS S E meaning smeaning resolution ctrs tots) cnf = true := by
  rw [centresK_eq] at ax
  have h0 : raw0.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard0 counts_ok totals_ok ax)
  have h1 : raw1.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard1 counts_ok totals_ok ax)
  have h2 : raw2.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard2 counts_ok totals_ok ax)
  have h3 : raw3.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard3 counts_ok totals_ok ax)
  have h4 : raw4.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard4 counts_ok totals_ok ax)
  have h5 : raw5.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard5 counts_ok totals_ok ax)
  have h6 : raw6.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard6 counts_ok totals_ok ax)
  have h7 : raw7.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard7 counts_ok totals_ok ax)
  have h8 : raw8.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard8 counts_ok totals_ok ax)
  have h9 : raw9.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard9 counts_ok totals_ok ax)
  have h10 : raw10.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard10 counts_ok totals_ok ax)
  have h11 : raw11.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard11 counts_ok totals_ok ax)
  have h12 : raw12.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard12 counts_ok totals_ok ax)
  have h13 : raw13.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard13 counts_ok totals_ok ax)
  have h14 : raw14.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard14 counts_ok totals_ok ax)
  have h15 : raw15.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard15 counts_ok totals_ok ax)
  have h16 : raw16.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard16 counts_ok totals_ok ax)
  have h17 : raw17.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard17 counts_ok totals_ok ax)
  have h18 : raw18.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard18 counts_ok totals_ok ax)
  have h19 : raw19.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard19 counts_ok totals_ok ax)
  have h20 : raw20.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard20 counts_ok totals_ok ax)
  have h21 : raw21.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard21 counts_ok totals_ok ax)
  have h22 : raw22.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard22 counts_ok totals_ok ax)
  have h23 : raw23.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard23 counts_ok totals_ok ax)
  have h24 : raw24.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard24 counts_ok totals_ok ax)
  have h25 : raw25.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard25 counts_ok totals_ok ax)
  have h26 : raw26.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard26 counts_ok totals_ok ax)
  have h27 : raw27.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard27 counts_ok totals_ok ax)
  have h28 : raw28.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard28 counts_ok totals_ok ax)
  have h29 : raw29.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard29 counts_ok totals_ok ax)
  have h30 : raw30.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard30 counts_ok totals_ok ax)
  have h31 : raw31.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard31 counts_ok totals_ok ax)
  have h32 : raw32.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard32 counts_ok totals_ok ax)
  have h33 : raw33.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard33 counts_ok totals_ok ax)
  have h34 : raw34.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard34 counts_ok totals_ok ax)
  have h35 : raw35.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard35 counts_ok totals_ok ax)
  have h36 : raw36.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard36 counts_ok totals_ok ax)
  have h37 : raw37.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard37 counts_ok totals_ok ax)
  have h38 : raw38.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard38 counts_ok totals_ok ax)
  have h39 : raw39.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard39 counts_ok totals_ok ax)
  have h40 : raw40.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard40 counts_ok totals_ok ax)
  have h41 : raw41.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard41 counts_ok totals_ok ax)
  have h42 : raw42.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard42 counts_ok totals_ok ax)
  have h43 : raw43.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard43 counts_ok totals_ok ax)
  have h44 : raw44.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard44 counts_ok totals_ok ax)
  have h45 : raw45.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard45 counts_ok totals_ok ax)
  have h46 : raw46.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard46 counts_ok totals_ok ax)
  have h47 : raw47.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard47 counts_ok totals_ok ax)
  have h48 : raw48.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard48 counts_ok totals_ok ax)
  have h49 : raw49.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard49 counts_ok totals_ok ax)
  have h50 : raw50.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard50 counts_ok totals_ok ax)
  have h51 : raw51.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard51 counts_ok totals_ok ax)
  have h52 : raw52.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard52 counts_ok totals_ok ax)
  have h53 : raw53.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard53 counts_ok totals_ok ax)
  have h54 : raw54.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard54 counts_ok totals_ok ax)
  have h55 : raw55.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard55 counts_ok totals_ok ax)
  have h56 : raw56.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard56 counts_ok totals_ok ax)
  have h57 : raw57.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard57 counts_ok totals_ok ax)
  have h58 : raw58.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard58 counts_ok totals_ok ax)
  have h59 : raw59.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard59 counts_ok totals_ok ax)
  have h60 : raw60.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard60 counts_ok totals_ok ax)
  have h61 : raw61.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard61 counts_ok totals_ok ax)
  have h62 : raw62.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard62 counts_ok totals_ok ax)
  have h63 : raw63.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard63 counts_ok totals_ok ax)
  have h64 : raw64.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard64 counts_ok totals_ok ax)
  have h65 : raw65.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard65 counts_ok totals_ok ax)
  have h66 : raw66.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard66 counts_ok totals_ok ax)
  have h67 : raw67.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard67 counts_ok totals_ok ax)
  have h68 : raw68.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard68 counts_ok totals_ok ax)
  have h69 : raw69.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard69 counts_ok totals_ok ax)
  have h70 : raw70.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard70 counts_ok totals_ok ax)
  have h71 : raw71.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard71 counts_ok totals_ok ax)
  have h72 : raw72.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard72 counts_ok totals_ok ax)
  have h73 : raw73.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard73 counts_ok totals_ok ax)
  have h74 : raw74.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard74 counts_ok totals_ok ax)
  have h75 : raw75.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard75 counts_ok totals_ok ax)
  have h76 : raw76.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard76 counts_ok totals_ok ax)
  have h77 : raw77.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard77 counts_ok totals_ok ax)
  have h78 : raw78.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard78 counts_ok totals_ok ax)
  have h79 : raw79.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard79 counts_ok totals_ok ax)
  have h80 : raw80.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard80 counts_ok totals_ok ax)
  have h81 : raw81.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard81 counts_ok totals_ok ax)
  have h82 : raw82.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard82 counts_ok totals_ok ax)
  have h83 : raw83.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard83 counts_ok totals_ok ax)
  have h84 : raw84.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard84 counts_ok totals_ok ax)
  have h85 : raw85.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard85 counts_ok totals_ok ax)
  have h86 : raw86.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard86 counts_ok totals_ok ax)
  have h87 : raw87.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard87 counts_ok totals_ok ax)
  have h88 : raw88.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard88 counts_ok totals_ok ax)
  have h89 : raw89.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard89 counts_ok totals_ok ax)
  have h90 : raw90.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard90 counts_ok totals_ok ax)
  have h91 : raw91.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard91 counts_ok totals_ok ax)
  have h92 : raw92.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard92 counts_ok totals_ok ax)
  have h93 : raw93.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard93 counts_ok totals_ok ax)
  have h94 : raw94.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard94 counts_ok totals_ok ax)
  have h95 : raw95.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard95 counts_ok totals_ok ax)
  have h96 : raw96.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard96 counts_ok totals_ok ax)
  have h97 : raw97.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard97 counts_ok totals_ok ax)
  have h98 : raw98.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard98 counts_ok totals_ok ax)
  have h99 : raw99.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard99 counts_ok totals_ok ax)
  have h100 : raw100.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard100 counts_ok totals_ok ax)
  have h101 : raw101.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard101 counts_ok totals_ok ax)
  have h102 : raw102.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard102 counts_ok totals_ok ax)
  have h103 : raw103.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard103 counts_ok totals_ok ax)
  have h104 : raw104.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard104 counts_ok totals_ok ax)
  have h105 : raw105.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard105 counts_ok totals_ok ax)
  have h106 : raw106.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard106 counts_ok totals_ok ax)
  simp only [cnf, cnfTrue, List.all_map, raw, List.all_append, Bool.and_eq_true,
    List.all_nil, and_true, and_assoc]
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h84, h85, h86, h87, h88, h89, h90, h91, h92, h93, h94, h95, h96, h97, h98, h99, h100, h101, h102, h103, h104, h105, h106⟩
#print axioms interpreted_core150
theorem local_share16_of_core_unsat150 (h : Unsat cnf) :
    RefutedShare window bounds resolution cap :=
  refutedShare_of_sat (fun S E ax => ⟨_, interpreted_core150 S E ax⟩) h
#print axioms local_share16_of_core_unsat150
end Snake9.LocalWindow.ShareWindow150
