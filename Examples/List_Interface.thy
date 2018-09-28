theory List_Interface
imports "../Refine_Imperative_HOL/Sepref"
begin

section "List Interface"


context
  fixes n::nat
begin
  definition "mop_empty_list = SPECT [ [] \<mapsto> enat n ]"

  sepref_register "mop_empty_list" 
  print_theorems 
end

context
  fixes t::"'a list \<Rightarrow>nat"
begin
  definition "mop_push_list  x xs = SPECT [ ( xs @ [x] ) \<mapsto> enat (t xs) ]"
  
  sepref_register "mop_push_list" 
  print_theorems
  thm   mop_push_list.pat
end


context
  fixes n::nat
begin
  definition "mop_lookup_list xs i = SPECT [ xs ! i \<mapsto> enat n ]"

  sepref_register "mop_lookup_list" 
  print_theorems 
end




end