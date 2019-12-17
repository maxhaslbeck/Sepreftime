chapter Sepreftime
                                            
session SeprefTime_Base = SepLogicTime_RBTreeBasic +
  sessions
    Flow_Networks
    EdmondsKarp_Maxflow
    Floyd_Warshall
    Case_Labeling
    Collections 
    "List-Index"
    "HOL-Library"
    Matroids
    "Automatic_Refinement"
  theories
    (* theory for Floyd Warshall *)
    "Floyd_Warshall.Floyd_Warshall"
    (* theories for Edmonds Karp *)
    "EdmondsKarp_Maxflow.EdmondsKarp_Termination_Abstract"
    (* theories for Kruskal *)
    "HOL-Library.Uprod"   
    Matroids.Matroid
    (* Misc *)
		"Refine_Monadic.Refine_Misc"
		"Refine_Monadic.RefineG_Domain"
    "Collections.Partial_Equivalence_Relation"
    "Case_Labeling.Case_Labeling"
    "List-Index.List_Index"
    "HOL-Library.Code_Target_Numeral"
    "Automatic_Refinement.Refine_Lib"
    "Automatic_Refinement.Automatic_Refinement" 

session SeprefTime = SeprefTime_Base + 
  sessions
    SepAuto_Time
    NREST
  theories
     "Examples/Examples"
