chapter SeprefTime

session SeprefTime_Base = HOL +
	sessions 
		SepLogicTime_RBTreeBasic
	theories
		"Refine_Monadic.Refine_Misc"
		"Refine_Monadic.RefineG_Domain"
 

session SeprefTime_HNR_Base = SeprefTime_Base + 
	theories
		"SepLogicTime_RBTreeBasic.SepAuto"
		Sepreftime

(*
session SeprefTime_RB = HOL +
	sessions 
		SepLogicTime_RBTreeBasic
	theories
		"Sepreftime"
		"SepLogicTime_RBTreeBasic.RBTree_Impl"
*)                                              

session EdmondsKarp_Time = SepLogicTime_RBTreeBasic +
  sessions
    Flow_Networks
    Case_Labeling
  theories
    "Examples/EdmondsKarp_Maxflow/EdmondsKarp_Time"