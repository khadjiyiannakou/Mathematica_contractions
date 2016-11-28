contract[expr_]:= Module[{listpsi, listpsib, listpsipsib, listpsibperms, signatures, contractions, exprbare, overallsign, npsis },
   listpsi  = Select[expr, (Head[#] == psi)&];
   listpsib = Select[expr, (Head[#] == psib)&];
   listpsipsib = Select[expr, (Head[#] == psib || Head[#] == psi)&];
   npsis = Length[listpsi];
   overallsign = (-1)^((npsis-1) npsis/2) *
      Product[(-1)^(Position[listpsipsib,psi][[i,1]] - i) ,{i, npsis}]; 
   listpsibperms = Permutations[listpsib];
   signatures = Signature[listpsib] (Signature /@ listpsibperms);
   exprbare = Times @@ Select[expr, (FreeQ[#,psi] && FreeQ[#,psib])&];
   contractions = overallsign *exprbare *
                    Sum[signatures[[k]] *
                        Product[If[listpsi[[l,4]] === listpsibperms[[k,l,4]],
                                   prop[listpsi[[l,1]], listpsibperms[[k,l,1]], 
                                        listpsi[[l,2]], listpsibperms[[k,l,2]],
                                        listpsi[[l,3]], listpsibperms[[k,l,3]], listpsi[[l,4]]],
                                   0],
                                {l, Length[listpsi]}], 
                        {k, Length[listpsibperms]}]]

{epsilon[b[1],b[2],b[3]],psi[x,b[1],j[1],u],cgamma5[j[1],j[2]],psi[x,b[2],j[2],d],psi[x,b[3],i[1],u],
 psib[y,b[4],j[3],u], gammaX[j[3],j[4]],psi[y,b[4],j[4],u],
 epsilon[b[5],b[6],b[7]],psib[z,b[7],i[2],u],psib[z,b[6],j[5],d],cgamma5[j[5],j[6]],psib[z,b[5],j[6],u]}

(* To select connected contractions only:
Select[Expand[%], (!MatchQ[#, _ prop[b_,b_,___]])&] // Factor
*)

(* To convert prop into uprop, dprop, etc. use:
% /. prop[a___,b_] :> ToExpression[StringJoin[ToString[b],"prop"]][a]
% //. uprop[a__,b_] :> uprop[a][b]
% //. dprop[a__,b_] :> dprop[a][b]
*)

rendermul[expr_Plus] := rendermul /@ expr 
rendermul[expr_Times] := Select[expr,FreeQ[#,prop]&] * rendermul[Select[expr,(!FreeQ[#,prop])&]] /; !(Select[expr,FreeQ[#,prop]&] === 1)
rendermul[a_] := a  /; (!(Head[a] === Times) && !(Head[a] === Plus))
rendermul[a_ b_ c___] :=  rendermul[mul[a,b] c] /; (!(Head[a] === Times) && !(Head[b] === Times))