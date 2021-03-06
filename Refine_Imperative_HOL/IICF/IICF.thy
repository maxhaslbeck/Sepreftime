section \<open>The Imperative Isabelle Collection Framework\<close>
theory IICF
imports        
  (* Sets *)
  "Intf/IICF_Set"

  "Impl/IICF_Rbt_Set"
  "Impl/IICF_List_Set"

  (* Maps *)
  "Intf/IICF_Map"

  "Impl/IICF_ArrayMap_Map"
  "Impl/IICF_RbtMap_Map"
  (*
  "Intf/IICF_Prio_Map"

  "Impl/Heaps/IICF_Impl_Heapmap" 
  *)

(*
  (* Multisets *)
  "Intf/IICF_Multiset"
  "Intf/IICF_Prio_Bag"

  "Impl/IICF_List_Mset"
  "Impl/IICF_List_MsetO"

  "Impl/Heaps/IICF_Impl_Heap"

*)
  (* Lists *)
  "Intf/IICF_List"

  "Impl/IICF_Array_ListN"
  "Impl/IICF_DArray_List"

 (* "Impl/IICF_Array" *)
(*
  "Impl/IICF_HOL_List"
  "Impl/IICF_Array_List"
  "Impl/IICF_Indexed_Array_List"
  "Impl/IICF_MS_Array_List"
*)
  (* Matrix *)
  "Intf/IICF_Matrix"

  "Impl/IICF_Array_Matrix"
(*
  (* Imports from Sep-Logic Entry*)
  "Impl/IICF_Sepl_Binding"
*)
begin
thy_deps
end
