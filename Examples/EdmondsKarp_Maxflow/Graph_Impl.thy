(* TODO: That's quite specific to the BFS alg. Move to Edka! *)
theory Graph_Impl (* copied from Flow_Networks.Graph_Impl *)
  imports (* Maxflow_Lib.Refine_Add_Fofu *)
    "../../Refine_Imperative_HOL/Sepref" 
    Flow_Networks.Graph
begin

\<comment> \<open>Fixing capacities to integer values\<close>
type_synonym capacity_impl = int (* TODO: DUP in Network_Impl. Remove here!*)
 


locale Impl_Succ =
  fixes absG :: "'ga \<Rightarrow> capacity_impl graph" 
  fixes ifT :: "'ig itself"
  fixes succ :: "'ga \<Rightarrow> node \<Rightarrow> node list nrest"
  fixes isG :: "'ga \<Rightarrow> 'gi \<Rightarrow> assn"
  fixes succ_impl :: "'gi \<Rightarrow> node \<Rightarrow> node list Heap"

  fixes  set_insert_time map_dom_member_time set_delete_time get_succs_list_time map_update_time set_pick_time :: nat
    and list_append_time map_lookup_time set_empty_time :: nat
  assumes [simp]: "map_lookup_time > 0"
  assumes [simp]: "set_pick_time > 0"

  (*assumes [constraint_rules]: "precise isG"*)
  assumes si_rule[sepref_fr_rules]: "(uncurry succ_impl,(uncurry succ)) \<in> [\<lambda>(c,u). u\<in>Graph.V (absG c)]\<^sub>a isG\<^sup>k *\<^sub>a (pure nat_rel)\<^sup>k \<rightarrow> list_assn (pure nat_rel)"
begin
  lemma this_loc: "Impl_Succ absG succ isG succ_impl map_lookup_time set_pick_time" apply unfold_locales apply simp apply simp 
    using si_rule .

  sepref_register "succ" :: "'ig \<Rightarrow> node \<Rightarrow> node list nrest" (* TODO: Will not work if succ is not a constant! *) 
end


end
