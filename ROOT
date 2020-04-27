chapter Sepreftime
                                            
session SeprefTime_Prereq in "SeprefTime_Prereq" = Imperative_HOL_Time_Entry +
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
  "Imperative_HOL_Time"
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
    "Imperative_HOL_Time.SLTC_Main"

session SeprefTime = SeprefTime_Prereq + 
  sessions
    NREST
  directories
    "Examples"
    "Examples/EdmondsKarp_Maxflow"
    "Examples/FloydWarshall"
    "Examples/Kruskal"

    "Refine_Imperative_HOL"
    "Refine_Imperative_HOL/Lib"
    "Refine_Imperative_HOL/IICF"
    "Refine_Imperative_HOL/IICF/Intf"
    "Refine_Imperative_HOL/IICF/Impl"

  theories
     "Examples/Examples"
