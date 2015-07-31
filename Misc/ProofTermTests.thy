theory ProofTermTests
imports
  Main
begin



thm Pure.conjunction_imp     
prf Pure.conjunction_imp
full_prf Pure.conjunction_imp


text {*  @{full_prf Pure.conjunction_imp}  *}
full_prf reflexive


ML {*
val _ = let
  val thy = @{theory Main};
  val ctxt = Proof_Context.init_global thy;
in
   writeln (Pretty.string_of 
     (Proof_Syntax.pretty_proof_of ctxt true
      @{thm Pure.conjunction_imp} ))
end
*}

unused_thms
thm_deps Pure.conjunction_imp


end
