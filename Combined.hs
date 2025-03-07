module Combined where

import Prelude
import Data.Tree
import TreePrint
import HG
import LIG
import LIGtoHG
import HGtoLIG

-- natural language categories
data Cats = VP | DPnom | DPdat | DPacc | V' | V | VEdat | VEacc | VE | TP | CP | WhP | DP | DPt deriving (Show, Eq)
data Case = Nom | Dat | Acc | Wh deriving (Show, Eq)

lig3r2 = Branch VP [DPdat] VP [] (Push Dat)
lig3r3 = Branch VP [DPacc] VP [] (Push Acc)
lig3r4 = Branch VP [] V' [V] (NoChange)
lig3r5 = Branch V' [] V' [VEdat] (Pop Dat)
lig3r6 = Branch V' [] V' [VEacc] (Pop Acc)
lig3r8 = Leaf V' [""]
lig3r9 = Leaf DPacc ["John.acc "]
lig3r10 = Leaf DPdat ["Peter.dat "]
lig3r11 = Leaf DPdat ["Mary.dat "]
lig3r12 = Leaf V ["swim "]
lig3r13 = Leaf VEdat ["teach.dat "]
lig3r14 = Leaf VEdat ["help.dat "]
lig3r15 = Leaf VEacc ["saw.acc "]

lig3t1 = LIT lig3r3 [
            LIT lig3r9 [],
            LIT lig3r2 [
                LIT lig3r10 [],
                LIT lig3r2 [
                    LIT lig3r11 [],
                    LIT lig3r4 [
                        LIT lig3r5 [
                            LIT lig3r5 [
                                LIT lig3r6 [
                                    LIT lig3r8 [],
                                    LIT lig3r15 []
                                ],
                                LIT lig3r14 []
                            ],
                            LIT lig3r13 []
                        ],
                        LIT lig3r12 []
                    ]
                ]
            ]
        ]


lig4r1 = Branch CP [WhP] TP [] (Push Wh)
lig4r2 = Branch TP [DP] VP [] (NoChange)
lig4r3 = Branch VP [VE] CP [] (NoChange)
lig4r4 = Branch CP [] TP [] (NoChange)
lig4r5 = Branch TP [DPt] VP [] (Pop Wh)
lig4r6 = Branch VP [] V [DPt] (Pop Wh)
lig4r7 = Leaf WhP ["which book "]
lig4r8 = Leaf DP ["the teacher "]
lig4r9 = Leaf VE ["asked "]
lig4r10 = Leaf WhP ["who "]
lig4r11 = Leaf DP ["Ivan "]
lig4r12 = Leaf VE ["helped "]
lig4r13 = Leaf DPt ["t "]
lig4r14 = Leaf V ["publish "]

-- lig4t1 :: LITree Cats VT Case
lig4t1 = LIT lig4r1 [
            LIT lig4r7 [],
            LIT lig4r2 [
                LIT lig4r8 [],
                LIT lig4r3 [
                    LIT lig4r9 [],
                    LIT lig4r1 [
                        LIT lig4r10 [],
                        LIT lig4r2 [
                            LIT lig4r11 [],
                            LIT lig4r3 [
                                LIT lig4r12 [],
                                LIT lig4r4 [
                                    LIT lig4r5 [
                                        LIT lig4r13 [],
                                        LIT lig4r6 [
                                            LIT lig4r14 [],
                                            LIT lig4r13 []
                                        ]
                                    ]
                                ]
                            ]
                        ]
                    ]
                ]
            ]
        ]



------------------
-- HG for cross serial

hg3r1 = Concat CP [DP] VP []
hg3r2 = Wrap VP CP VE
hg3r3 = Concat VP [] V []
hg3r4 = Leafh DP [] ["Jan "]
hg3r5 = Leafh VE [] ["saw "]
hg3r6 = Leafh DP [] ["Piet "]
hg3r7 = Leafh VE [] ["help "]
hg3r8 = Leafh DP [] ["the children "]
hg3r9 = Leafh V [] ["swim "]

hg3t1 = HGT hg3r1 [
            HGT hg3r4 [],
            HGT hg3r2 [
                HGT hg3r1 [
                    HGT hg3r6 [],
                    HGT hg3r2 [
                        HGT hg3r1 [
                            HGT hg3r8 [],
                            HGT hg3r3 [
                                HGT hg3r9 []
                            ]
                        ],
                        HGT hg3r7 []
                    ]
                ],
                HGT hg3r5 []
            ]
        ]