import Std

def passFail (ok : Bool) : String :=
  if ok then "PASS" else "FAIL"

def checkFloat (name : String) (lower threshold : Float) : IO Bool := do
  let ok := lower > threshold
  IO.println s!"{name}: lower={lower}, threshold={threshold}, {passFail ok}"
  pure ok

def checkSign (name : String) (value : Int) (wantPositive : Bool) : IO Bool := do
  let ok := if wantPositive then value > 0 else value < 0
  let want := if wantPositive then "> 0" else "< 0"
  IO.println s!"{name}: value {want}, actual={value}, {passFail ok}"
  pure ok

def quadNum (a b c n d : Int) : Int :=
  a*n*n + b*n*d + c*d*d

def cubicNum (a b c e n d : Int) : Int :=
  a*n*n*n + b*n*n*d + c*n*d*d + e*d*d*d

def quarticNum (a b c e f n d : Int) : Int :=
  a*n*n*n*n + b*n*n*n*d + c*n*n*d*d + e*n*d*d*d + f*d*d*d*d

def logLower (terms : List (Float × Float)) : Float :=
  - terms.foldl (fun acc (w, dist) => acc + w * Float.log dist) 0.0

def runThreeAtom : IO Bool := do
  IO.println "\nA. Fixed three-atom certificate candidate M=1.7877"
  let M := 1.7877
  let A := 1.27383
  let B := 0.34979
  let D := 2.73436
  let sqrt2m1 := Float.sqrt 2.0 - 1.0

  let qA : Int := 13118100000
  let qB : Int := -43152446909
  let qC : Int := 24441076860
  let den : Int := 100000000

  let s1 ← checkSign "three r1 left" (quadNum qA qB qC 72710566 den) true
  let s2 ← checkSign "three r1 right" (quadNum qA qB qC 72710567 den) false
  let s3 ← checkSign "three r2 left" (quadNum qA qB qC 256242916 den) false
  let s4 ← checkSign "three r2 right" (quadNum qA qB qC 256242917 den) true

  let v0 := logLower [(1.0, sqrt2m1), (A, M - sqrt2m1), (B, D - sqrt2m1)]
  let v1 := logLower [(1.0, 0.72710567), (A, M - 0.72710566), (B, D - 0.72710566)]
  let v2 := logLower [(1.0, 2.56242917), (A, 2.56242917 - M), (B, D - 2.56242916)]
  let v3 := logLower [(1.0, 1.0 + M), (A, 1.0), (B, 1.0 + M - D)]

  let c1 ← checkFloat "three V(sqrt2-1)" v0 (1827.0 / 10000.0)
  let c2 ← checkFloat "three V(r1 bracket)" v1 (223.0 / 10000000.0)
  let c3 ← checkFloat "three V(r2 bracket)" v2 (103.0 / 2500000.0)
  let c4 ← checkFloat "three V(1+M)" v3 (13.0 / 312500.0)
  pure ([s1, s2, s3, s4, c1, c2, c3, c4].all id)

def runThreeAtom178772 : IO Bool := do
  IO.println "\nB. Pushed three-atom certificate candidate M=1.78772"
  let M := 44693.0 / 25000.0
  let A := 127437.0 / 100000.0
  let B := 87431.0 / 250000.0
  let D := 546881.0 / 200000.0
  let sqrt2m1 := Float.sqrt 2.0 - 1.0

  let qA : Int := 262409400000
  let qB : Int := -863197728913
  let qC : Int := 488835050660
  let den : Int := 100000000

  let s1 ← checkSign "three M=1.78772 r1 left" (quadNum qA qB qC 72696113 den) true
  let s2 ← checkSign "three M=1.78772 r1 right" (quadNum qA qB qC 72696114 den) false
  let s3 ← checkSign "three M=1.78772 r2 left" (quadNum qA qB qC 256254651 den) false
  let s4 ← checkSign "three M=1.78772 r2 right" (quadNum qA qB qC 256254652 den) true

  let v0 := logLower [(1.0, sqrt2m1), (A, M - sqrt2m1), (B, D - sqrt2m1)]
  let v1 := logLower [(1.0, 0.72696114), (A, M - 0.72696113), (B, D - 0.72696113)]
  let v2 := logLower [(1.0, 2.56254652), (A, 2.56254652 - M), (B, D - 2.56254651)]
  let v3 := logLower [(1.0, 1.0 + M), (A, 1.0), (B, 1.0 + M - D)]

  let c1 ← checkFloat "three M=1.78772 V(sqrt2-1)" v0 (1825.0 / 10000.0)
  let c2 ← checkFloat "three M=1.78772 V(r1 bracket)" v1 (4.0 / 1000000.0)
  let c3 ← checkFloat "three M=1.78772 V(r2 bracket)" v2 (4.0 / 1000000.0)
  let c4 ← checkFloat "three M=1.78772 V(1+M)" v3 (4.0 / 1000000.0)
  pure ([s1, s2, s3, s4, c1, c2, c3, c4].all id)

def runThreeAtom178771 : IO Bool := do
  IO.println "\nB0. Forum-stable pushed three-atom certificate candidate M=1.78771"
  let M := 178771.0 / 100000.0
  let A := 637013.0 / 500000.0
  let B := 349761.0 / 1000000.0
  let D := 273438.0 / 100000.0
  let sqrt2m1 := Float.sqrt 2.0 - 1.0

  let qA : Int := 262378700000
  let qB : Int := -863103245119
  let qC : Int := 488827846980
  let den : Int := 100000000

  let s1 ← checkSign "three M=1.78771 r1 left" (quadNum qA qB qC 72705510 den) true
  let s2 ← checkSign "three M=1.78771 r1 right" (quadNum qA qB qC 72705511 den) false
  let s3 ← checkSign "three M=1.78771 r2 left" (quadNum qA qB qC 256247733 den) false
  let s4 ← checkSign "three M=1.78771 r2 right" (quadNum qA qB qC 256247734 den) true

  let v0 := logLower [(1.0, sqrt2m1), (A, M - sqrt2m1), (B, D - sqrt2m1)]
  let v1 := logLower [(1.0, 0.72705511), (A, M - 0.72705510), (B, D - 0.72705510)]
  let v2 := logLower [(1.0, 2.56247734), (A, 2.56247734 - M), (B, D - 2.56247733)]
  let v3 := logLower [(1.0, 1.0 + M), (A, 1.0), (B, 1.0 + M - D)]

  let c1 ← checkFloat "three M=1.78771 V(sqrt2-1)" v0 (1826.0 / 10000.0)
  let c2 ← checkFloat "three M=1.78771 V(r1 bracket)" v1 (15.0 / 1000000.0)
  let c3 ← checkFloat "three M=1.78771 V(r2 bracket)" v2 (15.0 / 1000000.0)
  let c4 ← checkFloat "three M=1.78771 V(1+M)" v3 (18.0 / 1000000.0)
  pure ([s1, s2, s3, s4, c1, c2, c3, c4].all id)

def runFourAtom : IO Bool := do
  IO.println "\nC. High-margin four-atom block"
  let w1 := 2457.0 / 2000.0
  let w2 := 767.0 / 5000.0
  let w3 := 1749.0 / 10000.0
  let s1f := 18003.0 / 10000.0
  let s2f := 26628.0 / 10000.0
  let s3f := 557.0 / 200.0

  let pA : Int := 319600000000
  let pB : Int := -1928087938750
  let pC : Int := 3492695976477
  let pD : Int := -1668855146175
  let den : Int := 100000000

  let r1l : Int := 74916852
  let r1r : Int := 74916853
  let r2l : Int := 254570327
  let r2r : Int := 254570328
  let r3l : Int := 273794401
  let r3r : Int := 273794402

  let s1 ← checkSign "four r1 left" (cubicNum pA pB pC pD r1l den) false
  let s2 ← checkSign "four r1 right" (cubicNum pA pB pC pD r1r den) true
  let s3 ← checkSign "four r2 left" (cubicNum pA pB pC pD r2l den) true
  let s4 ← checkSign "four r2 right" (cubicNum pA pB pC pD r2r den) false
  let s5 ← checkSign "four r3 left" (cubicNum pA pB pC pD r3l den) false
  let s6 ← checkSign "four r3 right" (cubicNum pA pB pC pD r3r den) true

  let v0 := logLower [(1.0, 0.7), (w1, s1f - 0.7), (w2, s2f - 0.7), (w3, s3f - 0.7)]
  let v1 := logLower [(1.0, 0.74916853), (w1, s1f - 0.74916852), (w2, s2f - 0.74916852), (w3, s3f - 0.74916852)]
  let v2 := logLower [(1.0, 2.54570328), (w1, 2.54570328 - s1f), (w2, s2f - 2.54570327), (w3, s3f - 2.54570327)]
  let v3 := logLower [(1.0, 2.73794402), (w1, 2.73794402 - s1f), (w2, 2.73794402 - s2f), (w3, s3f - 2.73794401)]
  let v4 := logLower [(1.0, 2.8), (w1, 2.8 - s1f), (w2, 2.8 - s2f), (w3, 2.8 - s3f)]

  let c1 ← checkFloat "four V(7/10)" v0 (7.0 / 1000.0)
  let c2 ← checkFloat "four V(r1 bracket)" v1 (9.0 / 2500.0)
  let c3 ← checkFloat "four V(r2 bracket)" v2 (7.0 / 1250.0)
  let c4 ← checkFloat "four V(r3 bracket)" v3 (7.0 / 2000.0)
  let c5 ← checkFloat "four V(14/5)" v4 (99.0 / 10000.0)
  pure ([s1, s2, s3, s4, s5, s6, c1, c2, c3, c4, c5].all id)

def runStronger1803Atom : IO Bool := do
  IO.println "\nD. Stronger four-atom block for M=1.803"
  let w1 := 6107.0 / 5000.0
  let w2 := 15563.0 / 100000.0
  let w3 := 4293.0 / 25000.0
  let s1f := 180321.0 / 100000.0
  let s2f := 266713.0 / 100000.0
  let s3f := 278795.0 / 100000.0

  let pA : Int := 2548750000000000
  let pB : Int := -15403293727600000
  let pC : Int := 27962858408259841
  let pD : Int := -13408354148818035
  let den : Int := 100000000

  let s1 ← checkSign "M=1.803 r1 left" (cubicNum pA pB pC pD 75277143 den) false
  let s2 ← checkSign "M=1.803 r1 right" (cubicNum pA pB pC pD 75277144 den) true
  let s3 ← checkSign "M=1.803 r2 left" (cubicNum pA pB pC pD 254863247 den) true
  let s4 ← checkSign "M=1.803 r2 right" (cubicNum pA pB pC pD 254863248 den) false
  let s5 ← checkSign "M=1.803 r3 left" (cubicNum pA pB pC pD 274206592 den) false
  let s6 ← checkSign "M=1.803 r3 right" (cubicNum pA pB pC pD 274206593 den) true

  let v0 := logLower [(1.0, 0.7), (w1, s1f - 0.7), (w2, s2f - 0.7), (w3, s3f - 0.7)]
  let v1 := logLower [(1.0, 0.75277144), (w1, s1f - 0.75277143), (w2, s2f - 0.75277143), (w3, s3f - 0.75277143)]
  let v2 := logLower [(1.0, 2.54863248), (w1, 2.54863248 - s1f), (w2, s2f - 2.54863247), (w3, s3f - 2.54863247)]
  let v3 := logLower [(1.0, 2.74206593), (w1, 2.74206593 - s1f), (w2, 2.74206593 - s2f), (w3, s3f - 2.74206592)]
  let v4 := logLower [(1.0, 2.803), (w1, 2.803 - s1f), (w2, 2.803 - s2f), (w3, 2.803 - s3f)]

  let c1 ← checkFloat "M=1.803 V(7/10)" v0 (49.0 / 10000.0)
  let c2 ← checkFloat "M=1.803 V(r1 bracket)" v1 (4.0 / 5000.0)
  let c3 ← checkFloat "M=1.803 V(r2 bracket)" v2 (39.0 / 50000.0)
  let c4 ← checkFloat "M=1.803 V(r3 bracket)" v3 (39.0 / 50000.0)
  let c5 ← checkFloat "M=1.803 V(2803/1000)" v4 (4.0 / 5000.0)
  pure ([s1, s2, s3, s4, s5, s6, c1, c2, c3, c4, c5].all id)

def runStronger18035Atom : IO Bool := do
  IO.println "\nE. Stronger four-atom block for M=1.8035"
  let w1 := 1214075.0 / 1000000.0
  let w2 := 78647.0 / 500000.0
  let w3 := 85271.0 / 500000.0
  let s1f := 18037.0 / 10000.0
  let s2f := 1333789.0 / 500000.0
  let s3f := 1394283.0 / 500000.0

  let pA : Int := 25419110000000000
  let pB : Int := -153688886076800000
  let pC : Int := 279228369532465741
  let pD : Int := -134172144177250476
  let den : Int := 100000000

  let s1 ← checkSign "M=1.8035 r1 left" (cubicNum pA pB pC pD 75523882 den) false
  let s2 ← checkSign "M=1.8035 r1 right" (cubicNum pA pB pC pD 75523883 den) true
  let s3 ← checkSign "M=1.8035 r2 left" (cubicNum pA pB pC pD 254795697 den) true
  let s4 ← checkSign "M=1.8035 r2 right" (cubicNum pA pB pC pD 254795698 den) false
  let s5 ← checkSign "M=1.8035 r3 left" (cubicNum pA pB pC pD 274299881 den) false
  let s6 ← checkSign "M=1.8035 r3 right" (cubicNum pA pB pC pD 274299882 den) true

  let v0 := logLower [(1.0, 0.7), (w1, s1f - 0.7), (w2, s2f - 0.7), (w3, s3f - 0.7)]
  let v1 := logLower [(1.0, 0.75523883), (w1, s1f - 0.75523882), (w2, s2f - 0.75523882), (w3, s3f - 0.75523882)]
  let v2 := logLower [(1.0, 2.54795698), (w1, 2.54795698 - s1f), (w2, s2f - 2.54795697), (w3, s3f - 2.54795697)]
  let v3 := logLower [(1.0, 2.74299882), (w1, 2.74299882 - s1f), (w2, 2.74299882 - s2f), (w3, s3f - 2.74299881)]
  let v4 := logLower [(1.0, 5607.0 / 2000.0), (w1, 5607.0 / 2000.0 - s1f), (w2, 5607.0 / 2000.0 - s2f), (w3, 5607.0 / 2000.0 - s3f)]

  let c1 ← checkFloat "M=1.8035 V(7/10)" v0 (48.0 / 10000.0)
  let c2 ← checkFloat "M=1.8035 V(r1 bracket)" v1 (25.0 / 100000.0)
  let c3 ← checkFloat "M=1.8035 V(r2 bracket)" v2 (26.0 / 100000.0)
  let c4 ← checkFloat "M=1.8035 V(r3 bracket)" v3 (25.0 / 100000.0)
  let c5 ← checkFloat "M=1.8035 V(5607/2000)" v4 (25.0 / 100000.0)
  pure ([s1, s2, s3, s4, s5, s6, c1, c2, c3, c4, c5].all id)

def runStronger18036Atom : IO Bool := do
  IO.println "\nF. Stronger four-atom block for M=1.8036"
  let w1 := 121285.0 / 100000.0
  let w2 := 158249.0 / 1000000.0
  let w3 := 169671.0 / 1000000.0
  let s1f := 9019.0 / 5000.0
  let s2f := 2667994.0 / 1000000.0
  let s3f := 2788781.0 / 1000000.0

  let pA : Int := 25407700000000000
  let pB : Int := -153643296691930000
  let pC : Int := 279201353231758683
  let pD : Int := -134210854692713932
  let den : Int := 100000000

  let s1 ← checkSign "M=1.8036 r1 left" (cubicNum pA pB pC pD 75565871 den) false
  let s2 ← checkSign "M=1.8036 r1 right" (cubicNum pA pB pC pD 75565872 den) true
  let s3 ← checkSign "M=1.8036 r2 left" (cubicNum pA pB pC pD 254792151 den) true
  let s4 ← checkSign "M=1.8036 r2 right" (cubicNum pA pB pC pD 254792152 den) false
  let s5 ← checkSign "M=1.8036 r3 left" (cubicNum pA pB pC pD 274353528 den) false
  let s6 ← checkSign "M=1.8036 r3 right" (cubicNum pA pB pC pD 274353529 den) true

  let v0 := logLower [(1.0, 0.7), (w1, s1f - 0.7), (w2, s2f - 0.7), (w3, s3f - 0.7)]
  let v1 := logLower [(1.0, 0.75565872), (w1, s1f - 0.75565871), (w2, s2f - 0.75565871), (w3, s3f - 0.75565871)]
  let v2 := logLower [(1.0, 2.54792152), (w1, 2.54792152 - s1f), (w2, s2f - 2.54792151), (w3, s3f - 2.54792151)]
  let v3 := logLower [(1.0, 2.74353529), (w1, 2.74353529 - s1f), (w2, 2.74353529 - s2f), (w3, s3f - 2.74353528)]
  let v4 := logLower [(1.0, 7009.0 / 2500.0), (w1, 7009.0 / 2500.0 - s1f), (w2, 7009.0 / 2500.0 - s2f), (w3, 7009.0 / 2500.0 - s3f)]

  let c1 ← checkFloat "M=1.8036 V(7/10)" v0 (47.0 / 10000.0)
  let c2 ← checkFloat "M=1.8036 V(r1 bracket)" v1 (14.0 / 100000.0)
  let c3 ← checkFloat "M=1.8036 V(r2 bracket)" v2 (14.0 / 100000.0)
  let c4 ← checkFloat "M=1.8036 V(r3 bracket)" v3 (15.0 / 100000.0)
  let c5 ← checkFloat "M=1.8036 V(7009/2500)" v4 (14.0 / 100000.0)
  pure ([s1, s2, s3, s4, s5, s6, c1, c2, c3, c4, c5].all id)

def runStronger1804Atom : IO Bool := do
  IO.println "\nG. Stronger five-atom block for M=1.804"
  let w1 := 1180333.0 / 1000000.0
  let w2 := 3543.0 / 125000.0
  let w3 := 117723.0 / 1000000.0
  let w4 := 179033.0 / 1000000.0
  let s1f := 9021.0 / 5000.0
  let s2f := 2571118.0 / 1000000.0
  let s3f := 2684011.0 / 1000000.0
  let s4f := 2788213.0 / 1000000.0

  let pA : Int := 1252716500000000000000000
  let pB : Int := -10827386081756000000000000
  let pC : Int := 33456188332790152991500000
  let pD : Int := -42486572502897050553224221
  let pE : Int := 17357490281503157606495400
  let den : Int := 100000000

  let s1 ← checkSign "M=1.804 r1 left" (quarticNum pA pB pC pD pE 76702920 den) true
  let s2 ← checkSign "M=1.804 r1 right" (quarticNum pA pB pC pD pE 76702921 den) false
  let s3 ← checkSign "M=1.804 r2 left" (quarticNum pA pB pC pD pE 252493236 den) false
  let s4 ← checkSign "M=1.804 r2 right" (quarticNum pA pB pC pD pE 252493237 den) true
  let s5 ← checkSign "M=1.804 r3 left" (quarticNum pA pB pC pD pE 260961793 den) true
  let s6 ← checkSign "M=1.804 r3 right" (quarticNum pA pB pC pD pE 260961794 den) false
  let s7 ← checkSign "M=1.804 r4 left" (quarticNum pA pB pC pD pE 274154611 den) false
  let s8 ← checkSign "M=1.804 r4 right" (quarticNum pA pB pC pD pE 274154612 den) true

  let v0 := logLower [(1.0, 0.7), (w1, s1f - 0.7), (w2, s2f - 0.7), (w3, s3f - 0.7), (w4, s4f - 0.7)]
  let v1 := logLower [(1.0, 0.76702921), (w1, s1f - 0.76702920), (w2, s2f - 0.76702920), (w3, s3f - 0.76702920), (w4, s4f - 0.76702920)]
  let v2 := logLower [(1.0, 2.52493237), (w1, 2.52493237 - s1f), (w2, s2f - 2.52493236), (w3, s3f - 2.52493236), (w4, s4f - 2.52493236)]
  let v3 := logLower [(1.0, 2.60961794), (w1, 2.60961794 - s1f), (w2, 2.60961794 - s2f), (w3, s3f - 2.60961793), (w4, s4f - 2.60961793)]
  let v4 := logLower [(1.0, 2.74154612), (w1, 2.74154612 - s1f), (w2, 2.74154612 - s2f), (w3, 2.74154612 - s3f), (w4, s4f - 2.74154611)]
  let v5 := logLower [(1.0, 701.0 / 250.0), (w1, 701.0 / 250.0 - s1f), (w2, 701.0 / 250.0 - s2f), (w3, 701.0 / 250.0 - s3f), (w4, 701.0 / 250.0 - s4f)]

  let c1 ← checkFloat "M=1.804 V(7/10)" v0 (47.0 / 5000.0)
  let c2 ← checkFloat "M=1.804 V(r1 bracket)" v1 (7.0 / 2500.0)
  let c3 ← checkFloat "M=1.804 V(r2 bracket)" v2 (7.0 / 2500.0)
  let c4 ← checkFloat "M=1.804 V(r3 bracket)" v3 (7.0 / 2500.0)
  let c5 ← checkFloat "M=1.804 V(r4 bracket)" v4 (7.0 / 2500.0)
  let c6 ← checkFloat "M=1.804 V(701/250)" v5 (7.0 / 2500.0)
  pure ([s1, s2, s3, s4, s5, s6, s7, s8, c1, c2, c3, c4, c5, c6].all id)

def runStronger1805Atom : IO Bool := do
  IO.println "\nH. Stronger five-atom block for M=1.805"
  let w1 := 117735.0 / 100000.0
  let w2 := 13473.0 / 500000.0
  let w3 := 23869.0 / 200000.0
  let w4 := 89427.0 / 500000.0
  let s1f := 9026.0 / 5000.0
  let s2f := 257054.0 / 100000.0
  let s3f := 134199.0 / 50000.0
  let s4f := 278919.0 / 100000.0

  let pA : Int := 12512475000000000000
  let pB : Int := -108165263291250000000
  let pC : Int := 334311904176703995000
  let pD : Int := -424736454351386263563
  let pE : Int := 173690901891803689848
  let den : Int := 100000000

  let s1 ← checkSign "M=1.805 r1 left" (quarticNum pA pB pC pD pE 76842878 den) true
  let s2 ← checkSign "M=1.805 r1 right" (quarticNum pA pB pC pD pE 76842879 den) false
  let s3 ← checkSign "M=1.805 r2 left" (quarticNum pA pB pC pD pE 252553845 den) false
  let s4 ← checkSign "M=1.805 r2 right" (quarticNum pA pB pC pD pE 252553846 den) true
  let s5 ← checkSign "M=1.805 r3 left" (quarticNum pA pB pC pD pE 260824271 den) true
  let s6 ← checkSign "M=1.805 r3 right" (quarticNum pA pB pC pD pE 260824272 den) false
  let s7 ← checkSign "M=1.805 r4 left" (quarticNum pA pB pC pD pE 274238380 den) false
  let s8 ← checkSign "M=1.805 r4 right" (quarticNum pA pB pC pD pE 274238381 den) true

  let v0 := logLower [(1.0, 0.7), (w1, s1f - 0.7), (w2, s2f - 0.7), (w3, s3f - 0.7), (w4, s4f - 0.7)]
  let v1 := logLower [(1.0, 0.76842879), (w1, s1f - 0.76842878), (w2, s2f - 0.76842878), (w3, s3f - 0.76842878), (w4, s4f - 0.76842878)]
  let v2 := logLower [(1.0, 2.52553846), (w1, 2.52553846 - s1f), (w2, s2f - 2.52553845), (w3, s3f - 2.52553845), (w4, s4f - 2.52553845)]
  let v3 := logLower [(1.0, 2.60824272), (w1, 2.60824272 - s1f), (w2, 2.60824272 - s2f), (w3, s3f - 2.60824271), (w4, s4f - 2.60824271)]
  let v4 := logLower [(1.0, 2.74238381), (w1, 2.74238381 - s1f), (w2, 2.74238381 - s2f), (w3, 2.74238381 - s3f), (w4, s4f - 2.74238380)]
  let v5 := logLower [(1.0, 561.0 / 200.0), (w1, 561.0 / 200.0 - s1f), (w2, 561.0 / 200.0 - s2f), (w3, 561.0 / 200.0 - s3f), (w4, 561.0 / 200.0 - s4f)]

  let c1 ← checkFloat "M=1.805 V(7/10)" v0 (84.0 / 10000.0)
  let c2 ← checkFloat "M=1.805 V(r1 bracket)" v1 (16.0 / 10000.0)
  let c3 ← checkFloat "M=1.805 V(r2 bracket)" v2 (16.0 / 10000.0)
  let c4 ← checkFloat "M=1.805 V(r3 bracket)" v3 (16.0 / 10000.0)
  let c5 ← checkFloat "M=1.805 V(r4 bracket)" v4 (159.0 / 100000.0)
  let c6 ← checkFloat "M=1.805 V(561/200)" v5 (16.0 / 10000.0)
  pure ([s1, s2, s3, s4, s5, s6, s7, s8, c1, c2, c3, c4, c5, c6].all id)

def runStronger1806Atom : IO Bool := do
  IO.println "\nI. Stronger five-atom block for M=1.806"
  let w1 := 29348.0 / 25000.0
  let w2 := 2657.0 / 100000.0
  let w3 := 5887.0 / 50000.0
  let w4 := 180873.0 / 1000000.0
  let s1f := 9031.0 / 5000.0
  let s2f := 25707.0 / 10000.0
  let s3f := 2683635.0 / 1000000.0
  let s4f := 2789842.0 / 1000000.0

  let pA : Int := 62477575000000000000
  let pB : Int := -540197265796625000000
  let pC : Int := 1670105544400391395000
  let pD : Int := -2122904930985962560404
  let pE : Int := 869081088441491719695
  let den : Int := 100000000

  let s1 ← checkSign "M=1.806 r1 left" (quarticNum pA pB pC pD pE 76998681 den) true
  let s2 ← checkSign "M=1.806 r1 right" (quarticNum pA pB pC pD pE 76998682 den) false
  let s3 ← checkSign "M=1.806 r2 left" (quarticNum pA pB pC pD pE 252599663 den) false
  let s4 ← checkSign "M=1.806 r2 right" (quarticNum pA pB pC pD pE 252599664 den) true
  let s5 ← checkSign "M=1.806 r3 left" (quarticNum pA pB pC pD pE 260818086 den) true
  let s6 ← checkSign "M=1.806 r3 right" (quarticNum pA pB pC pD pE 260818087 den) false
  let s7 ← checkSign "M=1.806 r4 left" (quarticNum pA pB pC pD pE 274209420 den) false
  let s8 ← checkSign "M=1.806 r4 right" (quarticNum pA pB pC pD pE 274209421 den) true

  let v0 := logLower [(1.0, 0.7), (w1, s1f - 0.7), (w2, s2f - 0.7), (w3, s3f - 0.7), (w4, s4f - 0.7)]
  let v1 := logLower [(1.0, 0.76998682), (w1, s1f - 0.76998681), (w2, s2f - 0.76998681), (w3, s3f - 0.76998681), (w4, s4f - 0.76998681)]
  let v2 := logLower [(1.0, 2.52599664), (w1, 2.52599664 - s1f), (w2, s2f - 2.52599663), (w3, s3f - 2.52599663), (w4, s4f - 2.52599663)]
  let v3 := logLower [(1.0, 2.60818087), (w1, 2.60818087 - s1f), (w2, 2.60818087 - s2f), (w3, s3f - 2.60818086), (w4, s4f - 2.60818086)]
  let v4 := logLower [(1.0, 2.74209421), (w1, 2.74209421 - s1f), (w2, 2.74209421 - s2f), (w3, 2.74209421 - s3f), (w4, s4f - 2.74209420)]
  let v5 := logLower [(1.0, 1403.0 / 500.0), (w1, 1403.0 / 500.0 - s1f), (w2, 1403.0 / 500.0 - s2f), (w3, 1403.0 / 500.0 - s3f), (w4, 1403.0 / 500.0 - s4f)]

  let c1 ← checkFloat "M=1.806 V(7/10)" v0 (75.0 / 10000.0)
  let c2 ← checkFloat "M=1.806 V(r1 bracket)" v1 (41.0 / 100000.0)
  let c3 ← checkFloat "M=1.806 V(r2 bracket)" v2 (41.0 / 100000.0)
  let c4 ← checkFloat "M=1.806 V(r3 bracket)" v3 (41.0 / 100000.0)
  let c5 ← checkFloat "M=1.806 V(r4 bracket)" v4 (41.0 / 100000.0)
  let c6 ← checkFloat "M=1.806 V(1403/500)" v5 (42.0 / 100000.0)
  pure ([s1, s2, s3, s4, s5, s6, s7, s8, c1, c2, c3, c4, c5, c6].all id)

def runStronger18063Atom : IO Bool := do
  IO.println "\nI2. Strongest five-atom block for M=1.8063"
  let w1 := 1174168821.0 / 1000000000.0
  let w2 := 25921118.0 / 1000000000.0
  let w3 := 118647936.0 / 1000000000.0
  let w4 := 180553554.0 / 1000000000.0
  let s1f := 180650001.0 / 100000000.0
  let s2f := 257053197.0 / 100000000.0
  let s3f := 268367709.0 / 100000000.0
  let s4f := 279017717.0 / 100000000.0

  let pA : Int := 833097143000000000000000000000000
  let pB : Int := -7203426448779519290000000000000000
  let pC : Int := 22271344049495468164668367700000000
  let pD : Int := -28310680823455635363669075998162907
  let pE : Int := 11590489097511299183527530554428470
  let den : Int := 100000000

  let s1 ← checkSign "M=1.8063 r1 left" (quarticNum pA pB pC pD pE 77003805 den) true
  let s2 ← checkSign "M=1.8063 r1 right" (quarticNum pA pB pC pD pE 77003806 den) false
  let s3 ← checkSign "M=1.8063 r2 left" (quarticNum pA pB pC pD pE 252642600 den) false
  let s4 ← checkSign "M=1.8063 r2 right" (quarticNum pA pB pC pD pE 252642601 den) true
  let s5 ← checkSign "M=1.8063 r3 left" (quarticNum pA pB pC pD pE 260759965 den) true
  let s6 ← checkSign "M=1.8063 r3 right" (quarticNum pA pB pC pD pE 260759966 den) false
  let s7 ← checkSign "M=1.8063 r4 left" (quarticNum pA pB pC pD pE 274249871 den) false
  let s8 ← checkSign "M=1.8063 r4 right" (quarticNum pA pB pC pD pE 274249872 den) true

  let v0 := logLower [(1.0, 0.7), (w1, s1f - 0.7), (w2, s2f - 0.7), (w3, s3f - 0.7), (w4, s4f - 0.7)]
  let v1 := logLower [(1.0, 0.77003806), (w1, s1f - 0.77003805), (w2, s2f - 0.77003805), (w3, s3f - 0.77003805), (w4, s4f - 0.77003805)]
  let v2 := logLower [(1.0, 2.52642601), (w1, 2.52642601 - s1f), (w2, s2f - 2.52642600), (w3, s3f - 2.52642600), (w4, s4f - 2.52642600)]
  let v3 := logLower [(1.0, 2.60759966), (w1, 2.60759966 - s1f), (w2, 2.60759966 - s2f), (w3, s3f - 2.60759965), (w4, s4f - 2.60759965)]
  let v4 := logLower [(1.0, 2.74249872), (w1, 2.74249872 - s1f), (w2, 2.74249872 - s2f), (w3, 2.74249872 - s3f), (w4, s4f - 2.74249871)]
  let v5 := logLower [(1.0, 28063.0 / 10000.0), (w1, 28063.0 / 10000.0 - s1f), (w2, 28063.0 / 10000.0 - s2f), (w3, 28063.0 / 10000.0 - s3f), (w4, 28063.0 / 10000.0 - s4f)]

  let c1 ← checkFloat "M=1.8063 V(7/10)" v0 (72.0 / 10000.0)
  let c2 ← checkFloat "M=1.8063 V(r1 bracket)" v1 (59.0 / 1000000.0)
  let c3 ← checkFloat "M=1.8063 V(r2 bracket)" v2 (58.0 / 1000000.0)
  let c4 ← checkFloat "M=1.8063 V(r3 bracket)" v3 (58.0 / 1000000.0)
  let c5 ← checkFloat "M=1.8063 V(r4 bracket)" v4 (57.0 / 1000000.0)
  let c6 ← checkFloat "M=1.8063 V(28063/10000)" v5 (59.0 / 1000000.0)
  pure ([s1, s2, s3, s4, s5, s6, s7, s8, c1, c2, c3, c4, c5, c6].all id)

structure IntervalBox where
  aLo : Float
  aHi : Float
  sLo : Float
  sHi : Float
  xLo : Float
  xHi : Float
  depth : Nat

structure IntervalStats where
  certified : Nat
  split : Nat
  worst : Float
  maxDepth : Nat
  failed : Bool

def iEps : Float := 1.0e-12
def iTarget : Float := 1.0e-6
def iMaxDepth : Nat := 40

def fAbs (x : Float) : Float :=
  if x < 0.0 then -x else x

def fMax (x y : Float) : Float :=
  if x >= y then x else y

def fMin (x y : Float) : Float :=
  if x <= y then x else y

def lowerNegLog (distance : Float) : Float :=
  -Float.log distance - iEps

def productLower (weightLo weightHi baseLo : Float) : Float :=
  if baseLo >= 0.0 then weightLo * baseLo else weightHi * baseLo

def conservativeCInterval (aLo aHi bLo bHi : Float) : Float × Float :=
  let numeratorLo :=
    -0.0001
    - Float.log (-1.0 - aLo)
    - (1.395 - bHi) * Float.log (1.0 + bHi)
    - iEps
  let numeratorHi :=
    -0.0001
    - Float.log (-1.0 - aHi)
    - (1.395 - bLo) * Float.log (1.0 + bLo)
    + iEps
  let denomLo := Float.log (2.071 - bHi) - iEps
  let denomHi := Float.log (2.071 - bLo) + iEps
  (numeratorLo / denomHi - iEps, numeratorHi / denomLo + iEps)

def intervalLowerBound (box : IntervalBox) : Float :=
  let lengthLo := 1.82 + box.aLo
  let lengthHi := 1.82 + box.aHi
  let bLo := box.sLo * lengthLo
  let bHi := box.sHi * lengthHi
  let cLo := 1.071 - bHi
  let cHi := 1.071 - bLo
  let cInt := conservativeCInterval box.aLo box.aHi bLo bHi
  let cLoWeight := cInt.fst
  let cHiWeight := cInt.snd
  let wLo := 1.395 - bHi
  let wHi := 1.395 - bLo
  let distA := box.xHi - box.aLo
  let baseA := lowerNegLog distA
  let distB := fMax (fAbs (box.xLo - bHi)) (fAbs (box.xHi - bLo))
  let baseB := lowerNegLog distB
  let distC := fMax (fAbs (box.xLo - cHi)) (fAbs (box.xHi - cLo))
  let baseC := lowerNegLog distC
  baseA
    + productLower wLo wHi baseB
    + productLower cLoWeight cHiWeight baseC

def splitIntervalBox (box : IntervalBox) : List IntervalBox :=
  let aW := box.aHi - box.aLo
  let sW := box.sHi - box.sLo
  let xW := box.xHi - box.xLo
  if aW >= sW && aW >= xW then
    let m := (box.aLo + box.aHi) / 2.0
    [
      { box with aHi := m, depth := box.depth + 1 },
      { box with aLo := m, depth := box.depth + 1 }
    ]
  else if sW >= xW then
    let m := (box.sLo + box.sHi) / 2.0
    [
      { box with sHi := m, depth := box.depth + 1 },
      { box with sLo := m, depth := box.depth + 1 }
    ]
  else
    let m := (box.xLo + box.xHi) / 2.0
    [
      { box with xHi := m, depth := box.depth + 1 },
      { box with xLo := m, depth := box.depth + 1 }
    ]

partial def intervalLoop (stack : List IntervalBox) (stats : IntervalStats) : IntervalStats :=
  match stack with
  | [] => stats
  | box :: rest =>
      let lower := intervalLowerBound box
      if lower > iTarget then
        intervalLoop rest {
          certified := stats.certified + 1,
          split := stats.split,
          worst := fMin stats.worst lower,
          maxDepth := Nat.max stats.maxDepth box.depth,
          failed := stats.failed
        }
      else if box.depth >= iMaxDepth then
        { stats with failed := true, worst := lower }
      else
        intervalLoop (splitIntervalBox box ++ rest) {
          certified := stats.certified,
          split := stats.split + 1,
          worst := stats.worst,
          maxDepth := stats.maxDepth,
          failed := stats.failed
        }

def runConservativeInterval : IO Bool := do
  IO.println "\nJ. Conservative forcing family interval-box numeric check"
  let start : IntervalBox := {
    aLo := -1.7,
    aHi := -1.414213562373095,
    sLo := 0.0,
    sHi := 1.0,
    xLo := 0.0,
    xHi := 1.0,
    depth := 0
  }
  let stats := intervalLoop [start] {
    certified := 0,
    split := 0,
    worst := 1.0e100,
    maxDepth := 0,
    failed := false
  }
  IO.println s!"certified boxes={stats.certified}, split boxes={stats.split}, max depth={stats.maxDepth}"
  IO.println s!"worst lower bound={stats.worst}"
  let ok := !stats.failed && stats.worst > iTarget
  IO.println s!"conservative interval check: {passFail ok}"
  pure ok

def main : IO Unit := do
  let ok1 ← runThreeAtom
  let ok178771 ← runThreeAtom178771
  let ok178772 ← runThreeAtom178772
  let ok2 ← runFourAtom
  let okStrong ← runStronger1803Atom
  let okStrong18035 ← runStronger18035Atom
  let okStrong18036 ← runStronger18036Atom
  let okStrong1804 ← runStronger1804Atom
  let okStrong1805 ← runStronger1805Atom
  let okStrong1806 ← runStronger1806Atom
  let okStrong18063 ← runStronger18063Atom
  let ok3 ← runConservativeInterval
  let ok := ok1 && ok178771 && ok178772 && ok2 && okStrong && okStrong18035 && okStrong18036 && okStrong1804 && okStrong1805 && okStrong1806 && okStrong18063 && ok3
  IO.println s!"\nOVERALL LEAN NUMERIC CHECK: {passFail ok}"
  if !ok then
    throw <| IO.userError "Lean certificate check failed"
