(* ::Package:: *)

(* ::Chapter:: *)
(*An Algebra For Conformal Gravity*)


(* ::Section:: *)
(*Definitions*)


(* ::Text:: *)
(*We are simply going to define equation 1.1 here. Since I don't like using numbers alone as labels due to mathematica being annoying, l[i] corresponds to the lower index of the Z_i's in 1.1.*)


c[{exp1_,exp2_,exp3_,exp4_}]:={{z[l[1]]^exp1*z[l[2]]^exp2*z[l[3]]^exp3*z[l[4]]^exp4,z[l[1]]},
{z[l[1]]^exp1*z[l[2]]^exp2*z[l[3]]^exp3*z[l[4]]^exp4,z[l[2]]},
{z[l[1]]^exp1*z[l[2]]^exp2*z[l[3]]^exp3*z[l[4]]^exp4,z[l[3]]},
{z[l[1]]^exp1*z[l[2]]^exp2*z[l[3]]^exp3*z[l[4]]^exp4,z[l[4]]}};


(* ::Text:: *)
(*We have a constraint for our C_A's.*)


cConstraint[expr_]:=expr/.{a1+a2+a3+a4->1,b1+b2+b3+b4->1}


(* ::Text:: *)
(*Define the commutator. First, we want to make sure we are multiplying/subtracting these things correctly.*)


csubtraction[subtract[a_,b_]]:=Module[{asc,asc1,asc2,values},
asc1=Map[pr,a,{1}]/.pr[{c_,d_}]:>Association[d->c];
asc2=Map[pr,b,{1}]/.pr[{c_,d_}]:>Association[d->-c];
asc=Merge[Flatten[{asc1,asc2}],Total];
MapThread[List,{Values[asc],Keys[asc]}]/.{0,c_}:>{0,0}
]


cproduct[c1_,c2_]:=Module[{str1,distribution1,rule,int,values,asc},
distribution1=Distribute[{c1,c2},List];
str1=Map[pr,distribution1,{1}];
rule=pr[{{a_,b_},{c_,d_}}]:>pr[{a*D[c,b],d}];
int=(str1/.rule)/.pr[{a_,b_}]:>Association[b->a];
asc=Merge[int,List];
values=Flatten[(Total/@{Values[asc]})];
MapThread[List,{values,Keys[asc]}]
]


cproduct[c[{a1,a2,a3,a4}],c[{b1,b2,b3,b4}]];


(* ::Text:: *)
(*Now, this is a preliminary commutator. We might want to add some things to this later as we test different generators of the subalgebras. *)


precommutator[{c1_,c2_}]:=subtract[cproduct[c1,c2],cproduct[c2,c1]];


precommutator[{c[{a1,a2,a3,a4}],c[{b1,b2,b3,b4}]}]


(* ::Text:: *)
(*This is 1.3.*)


(* ::Subsection:: *)
(*Global Subalgebra so(4,2)*)


(* ::Text:: *)
(*We can find the generators:*)


generators=Flatten[c[#]&/@Permutations[{1,0,0,0}],1][[1;;-2]]


(* ::Text:: *)
(*This is long but basically, just did the commutators for all the generators*)


applycommutators=(Map[Abs,Flatten[(csubtraction/@(precommutator/@Map[List,Distribute[{generators,generators},List],{2}])),1],{2}]//DeleteDuplicates)/.Abs[x_]:>x


(* ::Section:: *)
(*\[CapitalLambda]-deformed w-algebra*)


(* ::Text:: *)
(*Here we will simply create a function that allows to choose which of the C_A's we want.*)


cLabeled[c_,l[a_]]:=Map[List,Select[c,#[[-1]]==z[l[a]]&],{1}][[1]];


cLabeled[c[{a1,a2,a3,a4}],l[1]]


(* ::Text:: *)
(*We will now define the generators. I chose to the give the constants some list structure so mathematica doesn't do funny stuff. Basically, we will treat constants separately from the Z's and merge them all together later.*)


\[CapitalLambda]generator[{p_,mbar_,m_}]:={{(1/2)(p+mbar-1),cLabeled[c[{p+mbar-2,p-mbar-1,-p+m+2,-p-m+2}],l[2]]},
{-(1/2)(p-mbar-1),cLabeled[c[{p+mbar-1,p-mbar-2,-p+m+2,-p-m+2}],l[1]]},
{+\[CapitalLambda](1/2)(-p+m+2),cLabeled[c[{p+mbar-1,p-mbar-1,-p+m+1,-p-m+2}],l[4]]},
{-\[CapitalLambda](1/2)(-p-m+2),cLabeled[c[{p+mbar-1,p-mbar-1,-p+m+2,-p-m+1}],l[3]]}}


(* ::Text:: *)
(*Now, we can check we get 1.5:*)


\[CapitalLambda]generator[{p,mbar,m}]


(* ::Text:: *)
(*I need to define an addition function that generalizes the subtraction function, since that one could only take two arguments. It works great for the commutator, but now I need to regroup all the sums I get from distributing.*)


caddition[add[list_]]:=Module[{asc,,mapfunction,elements,associations,values},
mapfunction[x_]:=Map[pr,x,{1}]/.pr[{c_,d_}]:>Association[d->c];
associations=Map[mapfunction,list,{1}];
asc=Merge[Flatten[{associations}],Total];
MapThread[List,{Values[asc],Keys[asc]}]/.{0,c_}:>{0,0}
]


(* ::Text:: *)
(*This mixed product is useful working with both the coefficients and the Z's*)


mixedproduct[a_,b_]:=Module[{first,second,third},
first=Flatten[Outer[product,a,b,1],1];
second=first/.product[{x_,y_},{z_,w_}]:>g[x*z,cproduct[y,w]];
third=add[second/.g[x_,{{y_,z_}}]:>{{x*y,z}}];
third//caddition]


(* ::Text:: *)
(*We can now define our commutator:*)


commutator[a_,b_]:=subtract[mixedproduct[a,b],mixedproduct[b,a]]//csubtraction


(* ::Text:: *)
(*And we can check we get 1.6!*)


(commutator[\[CapitalLambda]generator[{p,mbar,m}],\[CapitalLambda]generator[{q,nbar,n}]]//FullSimplify)


(* ::Section:: *)
(*Finding a new basis for the algebra*)


(* ::Subsection:: *)
(*r and t generators*)


(* ::Subsubsection:: *)
(*Definitions*)


(* ::Text:: *)
(*Same as above, we want to define all our basis elements*)


rGenerator[{a_,b_,c1_,d_}]:={{a,cLabeled[c[{a-1,b,c1,d}],l[2]]},
{-b,cLabeled[c[{a,b-1,c1,d}],l[1]]}}


tGenerator[{a_,b_,c1_,d_}]:={{c1,cLabeled[c[{a,b,c1-1,d}],l[4]]},
{-d,cLabeled[c[{a,b,c1,d-1}],l[3]]}}


(* ::Subsubsection:: *)
(*Commutation relations*)


(* ::Text:: *)
(*Commutator [r,r]*)


rrcomm=commutator[rGenerator[{a1,a2,a3,a4}],rGenerator[{b1,b2,b3,b4}]]//FullSimplify


(* ::Text:: *)
(*Commutator [t,t]*)


ttcomm=commutator[tGenerator[{a1,a2,a3,a4}],tGenerator[{b1,b2,b3,b4}]]//FullSimplify


(* ::Text:: *)
(*Commutator [r,t]*)


rtcomm=commutator[rGenerator[{a1,a2,a3,a4}],tGenerator[{b1,b2,b3,b4}]]//FullSimplify


(* ::Subsubsection::Closed:: *)
(*Plus basis (probably will delete later)*)


(* ::Text:: *)
(*Basis elements:*)


rplus[{a_,b_,c1_,d_}]:={{a,cLabeled[c[{a-1,b,c1,d}],l[2]]},
{b,cLabeled[c[{a,b-1,c1,d}],l[1]]}}


tplus[{a_,b_,c1_,d_}]:={{c1,cLabeled[c[{a,b,c1-1,d}],l[4]]},
{d,cLabeled[c[{a,b,c1,d-1}],l[3]]}}


(* ::Text:: *)
(*Commutators:*)


rplusrplus=commutator[rplus[{a1,a2,a3,a4}],rplus[{b1,b2,b3,b4}]]//FullSimplify


commutator[tplus[{a1,a2,a3,a4}],tplus[{b1,b2,b3,b4}]]//FullSimplify


commutator[rGenerator[{a1,a2,a3,a4}],rplus[{b1,b2,b3,b4}]]//FullSimplify


(* ::Text:: *)
(*Finding [r+,r+] in terms of r^+ and r:*)


(* ::Text:: *)
(*-These two test functions are simply to add some coefficient in from of r and r+*)


rtestPlus=Flatten[(rplus[{a1+b1-1,a2+b2-1,a3+b3,a4+b4}])/.{x_,{{y_,z_}}}:>{{f*x*y,z}},1];


rtestMinus=Flatten[(rGenerator[{a1+b1-1,a2+b2-1,a3+b3,a4+b4}])/.{x_,{{y_,z_}}}:>{{g*x*y,z}},1];


testingrGenerator[frep_,grep_]:=add[{rtestPlus/.f->frep,rtestMinus/.g->grep}]//caddition


testingrGenerator[f,g]//FullSimplify


(* ::Text:: *)
(*-The target polynomials are the polynomials showing up in front of C_2 and C_1 in [r+,r+]*)


targetpolynomialc2[a1_,a2_,b1_,b2_]:=(a2 b1 (-1-a1+b1)+a1 (1-a1+b1) b2)//Expand ;


targetpolynomialc1[a1_,a2_,b1_,b2_]:=(-a2^2 b1+a1 (-1+b2) b2+a2 (b1-a1 b2+b1 b2))//Expand;


(* ::Text:: *)
(*-The test functions are our ansatz for the coefficients:*)


testfunction1[a1_,a2_,b1_,b2_]:=(1/2)((targetpolynomialc2[a1,a2,b1,b2]/(a1+b1-1))+(targetpolynomialc1[a1,a2,b1,b2]/(a2+b2-1)));


testfunction2[a1_,a2_,b1_,b2_]:=(1/2)((targetpolynomialc2[a1,a2,b1,b2]/(a1+b1-1))-(targetpolynomialc1[a1,a2,b1,b2]/(a2+b2-1)));


(* ::Text:: *)
(*-Finally, we want to see that the expressions we get after including our coefficients is the same as [r^+,r^+]*)


finalrtest=testingrGenerator[testfunction1[a1,a2,b1,b2],testfunction2[a1,a2,b1,b2]]//FullSimplify


finalrtest===rplusrplus


(* ::Text:: *)
(*Great!*)


(* ::Text:: *)
(*-Thinking about going from r and t to u and v:*)


testfunction1[p+mbar-1,p-mbar-1,q+nbar-1,1-nbar-1]//FullSimplify


testfunction2[p+mbar-1,p-mbar-1,q+nbar-1,1-nbar-1]//FullSimplify


(* ::Subsection:: *)
(*Dilatation and H generators*)


(* ::Subsubsection::Closed:: *)
(*Definitions and basic commutators*)


(* ::Text:: *)
(*We are doing to define our dilatation generators and the generators of the ideal H. We have for H[b_i] and D[b_i] the constraint that \sum b_i = 0. In order to make our commutation relations nicer, we can define the b_i constraint:*)


biConstraint[expr_]:=expr//.{a1+a2+a3+a4->0,b1+b2+b3+b4->0,-a1-a2-a3-a4->0,-b1-b2-b3-b4->0,{0,c_}:>{0,0}}


(* ::Text:: *)
(*We define the dilatation generator below:*)


dGenerator[{a_,b_,c1_,d_}]:={{1,cLabeled[c[{a+1,b,c1,d}],l[1]]},
{1,cLabeled[c[{a,b+1,c1,d}],l[2]]},
{-1,cLabeled[c[{a,b,c1+1,d}],l[3]]},
{-1,cLabeled[c[{a,b,c1,d+1}],l[4]]}}


(* ::Text:: *)
(*Then, we commutator [D,D]:*)


dDcomm=commutator[dGenerator[{a1,a2,a3,a4}],dGenerator[{b1,b2,b3,b4}]]//FullSimplify


(* ::Text:: *)
(*which gives another dilation D[a_i+b_i].*)
(*Then, we define our H generators:*)


hGenerator[{a_,b_,c1_,d_}]:={{1,cLabeled[c[{a+1,b,c1,d}],l[1]]},
{1,cLabeled[c[{a,b+1,c1,d}],l[2]]},
{1,cLabeled[c[{a,b,c1+1,d}],l[3]]},
{1,cLabeled[c[{a,b,c1,d+1}],l[4]]}}


(* ::Text:: *)
(*We compute the commutator [H,H]*)


commutator[hGenerator[{a1,a2,a3,a4}],hGenerator[{b1,b2,b3,b4}]]//FullSimplify//biConstraint


(* ::Text:: *)
(*We can see the H generators commute with each other.*)


(* ::Subsubsection:: *)
(*Commutators with C_A, r and t. *)


(* ::Text:: *)
(*Now, we want to make sure that [H,C_A] for some generic C_A returns ~ H*)


arbitraryc[{a_,b_,c1_,d_,e_}]:={{1,cLabeled[c[{a,b,c1,d}],l[e]]}}


commutator[hGenerator[{a1,a2,a3,a4}],arbitraryc[{b1,b2,b3,b4,1}]]//FullSimplify//cConstraint


(* ::Text:: *)
(*This gives us H[a1+b1-1, a_i+b_i]. *)


(* ::Text:: *)
(* [r,D];*)


rDcomm=(commutator[rGenerator[{a1,a2,a3,a4}],dGenerator[{b1,b2,b3,b4}]]//FullSimplify)/.{-a3-a4->-2+a1+a2,a3+a4->2-a1-a2}//FullSimplify


(* ::Text:: *)
(*Then, [t,D]:*)


tDcomm=(commutator[tGenerator[{a1,a2,a3,a4}],dGenerator[{b1,b2,b3,b4}]]//FullSimplify)/.{-a1-a2->-2+a3+a4,a1+a2->2-a3-a4}//FullSimplify


(* ::Text:: *)
(*Finally, [r,t]*)


(commutator[rGenerator[{a1,a2,a3,a4}],tGenerator[{b1,b2,b3,b4}]]//FullSimplify)


(* ::Subsection::Closed:: *)
(*Writing C_A in terms of r,t,D,H*)


(* ::Text:: *)
(*We are going to add a coefficient in front of each generator, and find C1 and C2 in terms of r, t, D and H:*)


rTest[{a1_,a2_,a3_,a4_}]:=rGenerator[{a1,a2,a3,a4}]/.{x_,{{y_,z_}}}:>{f*x*y,z}


tTest[{a1_,a2_,a3_,a4_}]:=tGenerator[{a1,a2,a3,a4}]/.{x_,{{y_,z_}}}:>{g*x*y,z}


dTest[{a1_,a2_,a3_,a4_}]:=dGenerator[{a1,a2,a3,a4}]/.{x_,{{y_,z_}}}:>{m*x*y,z}


hTest[{a1_,a2_,a3_,a4_}]:=hGenerator[{a1,a2,a3,a4}]/.{x_,{{y_,z_}}}:>{k*x*y,z}


(* ::Subsubsection:: *)
(*Rewriting C1 and C2*)


(* ::Text:: *)
(*Set g=0, then this set of rules should allow us to isolate C1 and C2:*)


c1Rules={k->m,k+m->-f-a1*f,f->-1/(2+a1+a2)};


c2Rules={k->m,k+m->f+a2*f,f->1/(2+a1+a2)};


(* ::Text:: *)
(*Check:*)


((add[{rTest[{a1+1,a2+1,a3,a4}],dTest[{a1,a2,a3,a4}],hTest[{a1,a2,a3,a4}]}]//caddition//FullSimplify)//.c1Rules//Simplify)/.{0,c_}:>{0,0}//Union


((add[{rTest[{a1+1,a2+1,a3,a4}],dTest[{a1,a2,a3,a4}],hTest[{a1,a2,a3,a4}]}]//caddition//FullSimplify)//.c2Rules//Simplify)/.{0,c_}:>{0,0}//Union


(* ::Subsubsection:: *)
(*Rewriting C3 and C4*)


(* ::Text:: *)
(*Set f=0, and this set of rules should allow us to isolate C3 and C4:*)


c3Rules={m->-k,k->-g((1+a3)/2),g->-1/(2+a3+a4)};


c4Rules={m->-k,k->g((1+a4)/2),g->1/(2+a3+a4)};


(* ::Text:: *)
(*Check:*)


((add[{tTest[{a1,a2,a3+1,a4+1}],dTest[{a1,a2,a3,a4}],hTest[{a1,a2,a3,a4}]}]//caddition//FullSimplify)//.c3Rules//Simplify)/.{0,c_}:>{0,0}//Union


((add[{tTest[{a1,a2,a3+1,a4+1}],dTest[{a1,a2,a3,a4}],hTest[{a1,a2,a3,a4}]}]//caddition//FullSimplify)//.c4Rules//Simplify)/.{0,c_}:>{0,0}//Union


(* ::Subsection::Closed:: *)
(*Rewriting the commutators as a linear combination of r, t, D and H*)


(* ::Subsubsection:: *)
(*[r,D] commutator*)


(* ::Text:: *)
(*Now, we can find the set of rules to express our commutator as a linear combination of r, D and H.*)


rDCommutatorRules={f->((2(a3+a4)(a1+a2))/(a1+b1+a2+b2)),
m->(a1*b2-a2*b1)(1+((a3+a4)/(a1+b1+a2+b2))),
k->(((a3+a4)/(a1+b1+a2+b2))(a1*b2-a2*b1))};


(((add[{rTest[{a1+b1,a2+b2,a3+b3,a4+b4}],dTest[{a1+b1-1,a2+b2-1,a3+b3,a4+b4}],
hTest[{a1+b1-1,a2+b2-1,a3+b3,a4+b4}]}]//caddition//FullSimplify)//.rDCommutatorRules)//FullSimplify)/.{-a3-a4->-2+a1+a2,a3+a4->2-a1-a2}//FullSimplify


(* ::Text:: *)
(*Check with the commutator:*)


(commutator[rGenerator[{a1,a2,a3,a4}],dGenerator[{b1,b2,b3,b4}]]//FullSimplify)/.{-a3-a4->-2+a1+a2,a3+a4->2-a1-a2}//FullSimplify


(-2 a1^2-a2 b1+a1 (4-2 a2+b2))//Expand


(-a2 b1+a1 (-2 (-2+a1+a2)+b2))//Expand


(* ::Text:: *)
(*We see they agree!*)


(* ::Subsubsection:: *)
(*[t,D] commutator*)


(* ::Text:: *)
(*Now, we can find the set of rules to express our commutator as a linear combination of t, D and H.*)


tDCommutatorRules={g->((-1)(2(a3+a4)(a1+a2))/(a3+b3+a4+b4)),
m->(a3*b4-a4*b3)(1-((-1)(a1+a2)/(a3+b3+a4+b4))),
k->((-1)((a1+a2)/(a3+b3+a4+b4))(a3*b4-a4*b3))};


(((add[{tTest[{a1+b1,a2+b2,a3+b3,a4+b4}],dTest[{a1+b1,a2+b2,a3+b3-1,a4+b4-1}],
hTest[{a1+b1,a2+b2,a3+b3-1,a4+b4-1}]}]//caddition//FullSimplify)//.tDCommutatorRules)//FullSimplify)/.{-a1-a2->-2+a3+a4,a1+a2->2-a3-a4}//FullSimplify


(* ::Text:: *)
(*Check with the commutator:*)


(commutator[tGenerator[{a1,a2,a3,a4}],dGenerator[{b1,b2,b3,b4}]]//FullSimplify)/.{-a1-a2->-2+a3+a4,a1+a2->2-a3-a4}//FullSimplify


(* ::Text:: *)
(*We see they agree!*)


(* ::Subsubsection:: *)
(*[r,t] commutator*)


(* ::Text:: *)
(*Now, we can find the set of rules to express our commutator as a linear combination of t, D and H.*)


rtCommutatorRules={f->(((a3*b4-a4*b3)(a1+a2))/(a1+a2+b1+b2)),
g->(((a1*b2-a2*b1)(b3+b4))/(a3+a4+b3+b4)),
m->(((a3*b4-a4*b3)(a1*b2-a2*b1))/(2(a1+a2+b1+b2)))+(((a3*b4-a4*b3)(a1*b2-a2*b1))/(2(a4+a3+b4+b3))),
k->(((a3*b4-a4*b3)(a1*b2-a2*b1))/(2(a1+a2+b1+b2)))+(-1)(((a3*b4-a4*b3)(a1*b2-a2*b1))/(2(a3+a4+b3+b4)))};


(((add[{rTest[{a1+b1,a2+b2,a3+b3-1,a4+b4-1}],dTest[{a1+b1-1,a2+b2-1,a3+b3-1,a4+b4-1}],tTest[{a1+b1-1,a2+b2-1,a3+b3,a4+b4}],
hTest[{a1+b1-1,a2+b2-1,a3+b3-1,a4+b4-1}]}]//caddition//FullSimplify)//.rtCommutatorRules)//FullSimplify)//Sort


(* ::Text:: *)
(*Check with the commutator:*)


(* ::Code::Initialization::Bold:: *)
(commutator[rGenerator[{a1,a2,a3,a4}],tGenerator[{b1,b2,b3,b4}]]//FullSimplify)//Sort


(* ::Text:: *)
(*They are the same!*)


(* ::Section::Closed:: *)
(*Celestial Basis*)


(* ::Subsection:: *)
(*Generators*)


uGenerator[{p_,mbar_,m_}]:=rGenerator[{p+mbar-1,p-mbar-1,-p+m+2,-p-m+2}]/.{x_,{{y_,z_}}}:>{(1/2)*x,{{y,z}}}


vGenerator[{p_,mbar_,m_}]:=tGenerator[{p+mbar-1,p-mbar-1,-p+m+2,-p-m+2}]/.{x_,{{y_,z_}}}:>{(1/2)*x,{{y,z}}}


dCelGenerator[{p_,mbar_,m_}]:=dGenerator[{p+mbar-1,p-mbar-1,-p+m+1,-p-m+1}]/.{x_,{{y_,z_}}}:>{(1/4)*x,{{y,z}}}


(* ::Subsection:: *)
(*Commutator relations*)


(* ::Subsubsection:: *)
(*[u,u] commutator*)


commutator[uGenerator[{p,mbar,m}],uGenerator[{q,nbar,n}]]//FullSimplify


(* ::Subsubsection:: *)
(*[v,v] commutator*)


commutator[vGenerator[{p,mbar,m}],vGenerator[{q,nbar,n}]]//FullSimplify


(* ::Subsubsection:: *)
(*[d,d] commutator*)


commutator[dCelGenerator[{p,mbar,m}],dCelGenerator[{q,nbar,n}]]//FullSimplify


(* ::Subsubsection:: *)
(*[u,d] commutator*)


commutator[uGenerator[{p,mbar,m}],dCelGenerator[{q,nbar,n}]]//FullSimplify


(* ::Subsubsection:: *)
(*[v,d] commutator*)


commutator[vGenerator[{p,mbar,m}],dCelGenerator[{q,nbar,n}]]//FullSimplify


(* ::Subsubsection:: *)
(*[u,v] commutator*)


commutator[uGenerator[{p,mbar,m}],vGenerator[{q,nbar,n}]]//FullSimplify


(* ::Subsection:: *)
(*Finding the commutator coefficients*)


(* ::Subsubsection:: *)
(*[u,d] commutator*)


uDCommutatorRules[{{p_,mbar_,m_},{q_,nbar_,n_}}]:=Module[{a1,a2,a3,a4,b1,b2,b3,b4},
a1=p+mbar-1;
a2=p-mbar-1;
a3=-p+m+2;
a4=-p-m+2;
b1=q+nbar-1;
b2=q-nbar-1;
b3=-q+n+1;
b4=-q-n+1;
{uCoefficient->((2(a3+a4)(a1+a2))/(a1+b1+a2+b2)),
dCoefficient->(a1*b2-a2*b1)(1+((a3+a4)/(a1+b1+a2+b2))),
hCoefficient->(((a3+a4)/(a1+b1+a2+b2))(a1*b2-a2*b1))}//FullSimplify]


uDCommutatorRules[{{p,mbar,m},{q,nbar,n}}]


(* ::Subsubsection:: *)
(*[v,d] commutator*)


vDCommutatorRules[{{p_,mbar_,m_},{q_,nbar_,n_}}]:=Module[{a1,a2,a3,a4,b1,b2,b3,b4},
a1=p+mbar-1;
a2=p-mbar-1;
a3=-p+m+2;
a4=-p-m+2;
b1=q+nbar-1;
b2=q-nbar-1;
b3=-q+n+1;
b4=-q-n+1;
{vCoefficient->((-1)(2(a3+a4)(a1+a2))/(a3+b3+a4+b4)),
dCoefficient->(a3*b4-a4*b3)(1-((-1)(a1+a2)/(a3+b3+a4+b4))),
hCoefficient->((-1)((a1+a2)/(a3+b3+a4+b4))(a3*b4-a4*b3))}//FullSimplify]


vDCommutatorRules[{{p,mbar,m},{q,nbar,n}}]


(* ::Subsubsection:: *)
(*[u,v] commutator*)


uvCommutatorRules[{{p_,mbar_,m_},{q_,nbar_,n_}}]:=Module[{a1,a2,a3,a4,b1,b2,b3,b4},
a1=p+mbar-1;
a2=p-mbar-1;
a3=-p+m+2;
a4=-p-m+2;
b1=q+nbar-1;
b2=q-nbar-1;
b3=-q+n+2;
b4=-q-n+2;
{uCoefficient->(((a3*b4-a4*b3)(a1+a2))/(a1+a2+b1+b2)),
vCoefficient->(((a1*b2-a2*b1)(b3+b4))/(a3+a4+b3+b4)),
dCoefficient->(((a3*b4-a4*b3)(a1*b2-a2*b1))/(2(a1+a2+b1+b2)))+(((a3*b4-a4*b3)(a1*b2-a2*b1))/(2(a4+a3+b4+b3))),
hCoefficient->(((a3*b4-a4*b3)(a1*b2-a2*b1))/(2(a1+a2+b1+b2)))+(-1)(((a3*b4-a4*b3)(a1*b2-a2*b1))/(2(a3+a4+b3+b4)))}//FullSimplify]


uvCommutatorRules[{{p,mbar,m},{q,nbar,n}}]


(* ::Section:: *)
(*Introducing a divergence operator*)


(* ::Text:: *)
(*Given a C_A, we are going to define a divergence operator:*)


div[{d_,list_}]:=Module[{pairs},
pairs=D[#[[1]],#[[-1]]]&/@list;
{d*pairs}]


applyDiv[basis_]:=Total@(div/@basis)//Flatten//FullSimplify


(* ::Text:: *)
(*We check if r, t and D are divergence free:*)


applyDiv[rGenerator[{a1,a2,a3,a4}]]


applyDiv[tGenerator[{a1,a2,a3,a4}]]


applyDiv[dGenerator[{a1,a2,a3,a4}]]


applyDiv[dGenerator[{a1,-a1,a3,-a3}]]//FullSimplify


(* ::Text:: *)
(*Now, we check if the commutators are divergence free. *)


commutatorToBasis[expr_]:={1,expr}


(* ::Text:: *)
(*First, for [r,r], [t,t], and [r,t] we get that the divergence vanishes:*)


rrdiv=(Total@(div[rrcomm//commutatorToBasis]//Flatten))//FullSimplify


ttdiv=(Total@(div[ttcomm//commutatorToBasis]//Flatten))//FullSimplify


rtdiv=(Total@(div[rtcomm//commutatorToBasis]//Flatten))//FullSimplify


(* ::Text:: *)
(*For [D,D], div [D,D] =/= 0 in general*)


dDdiv=(Total@(div[dDcomm//commutatorToBasis]//Flatten))//FullSimplify


(* ::Text:: *)
(*unless we constraint a2=-a1,  a4=-a3, b2=-b1, b4=-b3*)


dDdiv/.{a2->-a1,a4->-a3,b2->-b1,b4->-b3}


(* ::Text:: *)
(*For [r[a_i],D[b_i]] and [t[a_i],D[b_i]] the divergence vanishes by sending b2=-b1 and b4=-b3 *)


rDdiv=((Total@(div[rDcomm//commutatorToBasis]//Flatten))//FullSimplify)/.a1+a2+a3+a4->2


tDdiv=((Total@(div[tDcomm//commutatorToBasis]//Flatten))//FullSimplify)/.a1+a2+a3+a4->2


(rDdiv/.{b2->-b1,b4->-b3}//FullSimplify)


(tDdiv/.{b2->-b1,b4->-b3}//FullSimplify)
