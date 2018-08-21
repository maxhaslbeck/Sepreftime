theory Example_Automatic
imports "Refine_Imperative_HOL/Sepref_Monadify"
begin


definition set_init_t :: "nat" where "set_init_t = 1"

definition set_init_SPEC :: "nat set nrest" where
  "set_init_SPEC \<equiv> SPECT [{} \<mapsto> set_init_t ]"

definition set_ins_t :: "nat\<Rightarrow>nat" where "set_ins_t n = (n+1)"

definition set_ins_SPEC where
  "set_ins_SPEC x S \<equiv> SPECT [insert x S \<mapsto> set_ins_t (card S)]"

fun set_mem_t :: "nat\<Rightarrow>nat" where "set_mem_t n = (n + 1)"

definition set_mem_SPEC where
  "set_mem_SPEC x S \<equiv> SPECT [ (x \<in> S) \<mapsto> set_mem_t (card S)]"



definition rd_impl1 :: "nat list \<Rightarrow> (nat list) nrest" where
  "rd_impl1 as = do {
          ys \<leftarrow> RETURNT [];
          S \<leftarrow> set_init_SPEC;
          zs \<leftarrow> RETURNT as;
          (zs,ys,S) \<leftarrow> whileT (\<lambda>(xs,ys,S). length xs > 0)
            (\<lambda>(xs,ys,S). do {                          
                          ASSERT (length xs > 0);
                          ASSERT (length xs + length ys \<le> length as);
                          ASSERT (card S \<le> length ys);
                          x \<leftarrow> RETURNT (hd xs);
                          xs \<leftarrow> RETURNT (tl xs);
                          b \<leftarrow> set_mem_SPEC x S;
                          (if b
  then  RETURNT (xs,ys,S)
  else do { S \<leftarrow> set_ins_SPEC x S;
            ys \<leftarrow> RETURNT (x#ys);  
            RETURNT (xs,ys,S)
  } ) }) (zs,ys,S);
          RETURNT ys
      }"


schematic_goal "hn_refine \<Gamma> ?c ?\<Gamma>' ?R (rd_impl1 as)"



end