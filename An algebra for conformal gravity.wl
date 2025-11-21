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
(*u and v basis set-up*)


(* ::Subsubsection:: *)
(*Definitions*)


(* ::Text:: *)
(*Pretty straightforward. 	We just want to write these new basis elements in the same format at the \LambdaGenerators to get the commutation relations.*)


uplus[{p_,mbar_,m_}]:={{(1/2)(p+mbar-1),cLabeled[c[{p+mbar-2,p-mbar-1,-p+m+2,-p-m+2}],l[2]]},
{+(1/2)(p-mbar-1),cLabeled[c[{p+mbar-1,p-mbar-2,-p+m+2,-p-m+2}],l[1]]}}


uminus[{p_,mbar_,m_}]:={{(1/2)(p+mbar-1),cLabeled[c[{p+mbar-2,p-mbar-1,-p+m+2,-p-m+2}],l[2]]},
{-(1/2)(p-mbar-1),cLabeled[c[{p+mbar-1,p-mbar-2,-p+m+2,-p-m+2}],l[1]]}}


vplus[{p_,mbar_,m_}]:={{+(1/2)(-p+m+2),cLabeled[c[{p+mbar-1,p-mbar-1,-p+m+1,-p-m+2}],l[4]]},
{+(1/2)(-p-m+2),cLabeled[c[{p+mbar-1,p-mbar-1,-p+m+2,-p-m+1}],l[3]]}}


vminus[{p_,mbar_,m_}]:={{+(1/2)(-p+m+2),cLabeled[c[{p+mbar-1,p-mbar-1,-p+m+1,-p-m+2}],l[4]]},
{-(1/2)(-p-m+2),cLabeled[c[{p+mbar-1,p-mbar-1,-p+m+2,-p-m+1}],l[3]]}}


(* ::Subsubsection:: *)
(*Commutation relations*)


(* ::Text:: *)
(*Commutator [ u^+,u^+]*)


commutator[uplus[{p,mbar,m}],uplus[{q,nbar,n}]]//FullSimplify


(* ::Text:: *)
(*Commutator [ u^-,u^-]*)


commutator[uminus[{p,mbar,m}],uminus[{q,nbar,n}]]//FullSimplify


(* ::Text:: *)
(*Commutator [ v^+,v^+]*)


commutator[vplus[{p,mbar,m}],vplus[{q,nbar,n}]]//FullSimplify


(* ::Text:: *)
(*Commutator [ v^-,v^-]*)


commutator[vminus[{p,mbar,m}],vminus[{q,nbar,n}]]//FullSimplify


(* ::Subsection:: *)
(*r and t basis set-up*)


(* ::Subsubsection:: *)
(*Definitions*)


(* ::Text:: *)
(*Same as above, we want to define all our basis elements*)


rminus[{a_,b_,c1_,d_}]:={{a,cLabeled[c[{a-1,b,c1,d}],l[2]]},
{-b,cLabeled[c[{a,b-1,c1,d}],l[1]]}}


rplus[{a_,b_,c1_,d_}]:={{a,cLabeled[c[{a-1,b,c1,d}],l[2]]},
{b,cLabeled[c[{a,b-1,c1,d}],l[1]]}}


tminus[{a_,b_,c1_,d_}]:={{c1,cLabeled[c[{a,b,c1-1,d}],l[4]]},
{-d,cLabeled[c[{a,b,c1,d-1}],l[3]]}}


tplus[{a_,b_,c1_,d_}]:={{c1,cLabeled[c[{a,b,c1-1,d}],l[4]]},
{d,cLabeled[c[{a,b,c1,d-1}],l[3]]}}


newtplus[a_,b_,c1_,d_]:={{1,cLabeled[c[a,b,c1,d],l[3]]}}


newrplus[a_,b_,c1_,d_]:={{1,cLabeled[c[a,b,c1,d],l[1]]}}


(* ::Subsubsection:: *)
(*Commutation relations*)


(* ::Text:: *)
(*Commutator [ r^-,r^-]*)


commutator[rminus[{a1,a2,a3,a4}],rminus[{b1,b2,b3,b4}]]//FullSimplify


(* ::Text:: *)
(*Commutator [ r^+,r^+]*)


rplusrplus=commutator[rplus[{a1,a2,a3,a4}],rplus[{b1,b2,b3,b4}]]//FullSimplify


(* ::Text:: *)
(*Commutator [ r^-,r^+]*)


commutator[rminus[{a1,a2,a3,a4}],rplus[{b1,b2,b3,b4}]]//FullSimplify


(* ::Text:: *)
(*so, [ r^+,r^+] and [ r^-,r^+] are quite similar.*)


(* ::Text:: *)
(*Commutator [ t^-,t^-]*)


commutator[tminus[{a1,a2,a3,a4}],tminus[{b1,b2,b3,b4}]]//FullSimplify


(* ::Text:: *)
(*Commutator [ t^+,t^+]*)


commutator[tplus[{a1,a2,a3,a4}],tplus[{b1,b2,b3,b4}]]//FullSimplify


(* ::Text:: *)
(*Commutator [ r^-,t^-]*)


commutator[rminus[{a1,a2,a3,a4}],tminus[{b1,b2,b3,b4}]]//FullSimplify


rminus[{a1+b1-1,a2+b2,a3+b3-1,a4+b4}]


(* ::Subsubsection:: *)
(*Finding [r^+,r^+] in terms of r^+ and r^-*)


(* ::Text:: *)
(*These two test functions are simply to add some coefficient in from of r^- and r^+*)


rtestPlus=Flatten[(rplus[{a1+b1-1,a2+b2-1,a3+b3,a4+b4}])/.{x_,{{y_,z_}}}:>{{f*x*y,z}},1];


rtestMinus=Flatten[(rminus[{a1+b1-1,a2+b2-1,a3+b3,a4+b4}])/.{x_,{{y_,z_}}}:>{{g*x*y,z}},1];


testingrGenerator[frep_,grep_]:=add[{rtestPlus/.f->frep,rtestMinus/.g->grep}]//caddition


testingrGenerator[f,g]//FullSimplify


(* ::Text:: *)
(*The target polynomials are the polynomials showing up in front of C_2 and C_1 in [r^+,r^+]*)


targetpolynomialc2[a1_,a2_,b1_,b2_]:=(a2 b1 (-1-a1+b1)+a1 (1-a1+b1) b2)//Expand ;


targetpolynomialc1[a1_,a2_,b1_,b2_]:=(-a2^2 b1+a1 (-1+b2) b2+a2 (b1-a1 b2+b1 b2))//Expand;


(* ::Text:: *)
(*The test functions are our ansatz for the coefficients:*)


testfunction1[a1_,a2_,b1_,b2_]:=(1/2)((targetpolynomialc2[a1,a2,b1,b2]/(a1+b1-1))+(targetpolynomialc1[a1,a2,b1,b2]/(a2+b2-1)));


testfunction2[a1_,a2_,b1_,b2_]:=(1/2)((targetpolynomialc2[a1,a2,b1,b2]/(a1+b1-1))-(targetpolynomialc1[a1,a2,b1,b2]/(a2+b2-1)));


(* ::Text:: *)
(*Finally, we want to see that the expressions we get after including our coefficients is the same as [r^+,r^+]*)


finalrtest=testingrGenerator[testfunction1[a1,a2,b1,b2],testfunction2[a1,a2,b1,b2]]//FullSimplify


finalrtest===rplusrplus


(* ::Text:: *)
(*Great!*)


(* ::Subsection:: *)
(*from r and t to u and v*)


testfunction1[p+mbar-1,p-mbar-1,q+nbar-1,1-nbar-1]//FullSimplify


testfunction2[p+mbar-1,p-mbar-1,q+nbar-1,1-nbar-1]//FullSimplify


(* ::Subsection::Closed:: *)
(*Testing for Polynomials*)


listOfPolynomials=Module[{list,secondlist,thirdlist, fourthlist},
list=Subsets[{a1,a2,b1,b2},{1,2}];
secondlist=Flatten[Complement[If[Length[#]==1,(#/.{y_}:>{{y},{y^2}}),#]&/@list,list],1];
thirdlist=Map[#/.List->Times&,Union[list,secondlist],2];
fourthlist=\[Alpha][#]&/@Range[Length[thirdlist]];
Total[MapThread[h,{thirdlist,fourthlist}]/.h->Times]];


listOfPolynomials


polynomialc2=(-1+a1+b1)(a1 \[Alpha][1]+a1^2 \[Alpha][2]+a2 \[Alpha][3]+a2^2 \[Alpha][4]+b1 \[Alpha][5]+b1^2 \[Alpha][6]+b2 \[Alpha][7]+b2^2 \[Alpha][8]+a1 a2 \[Alpha][9]+a1 b1 \[Alpha][10]+a1 b2 \[Alpha][11]+a2 b1 \[Alpha][12]+a2 b2 \[Alpha][13]+b1 b2 \[Alpha][14])//Expand;


polynomialc1=(1-a2-b2)(a1 \[Alpha][1]+a1^2 \[Alpha][2]+a2 \[Alpha][3]+a2^2 \[Alpha][4]+b1 \[Alpha][5]+b1^2 \[Alpha][6]+b2 \[Alpha][7]+b2^2 \[Alpha][8]+a1 a2 \[Alpha][9]+a1 b1 \[Alpha][10]+a1 b2 \[Alpha][11]+a2 b1 \[Alpha][12]+a2 b2 \[Alpha][13]+b1 b2 \[Alpha][14])//Expand;








CoefficientArrays[{targetpolynomialc2-polynomialc2== 0}, {a1, a2, 
  b1,b2}]


diff2 = Expand[targetpolynomialc2 - polynomialc2];

{const, linear, quad, cross} = CoefficientArrays[diff, {a1, a2, b1, b2}];

allCoeffs2 = Join[
    {const},
    Normal[linear],
    Flatten[Normal[quad]],
    Flatten[Normal[cross]]
];

eqs2 = Thread[allCoeffs == 0];

Reduce[eqs2]


eqs


diff1 = Expand[targetpolynomialc1 - polynomialc1];

{const, linear, quad, cross} = CoefficientArrays[diff, {a1, a2, b1, b2}];

allCoeffs1 = Join[
    {const},
    Normal[linear],
    Flatten[Normal[quad]],
    Flatten[Normal[cross]]
];

eqs1 = Thread[allCoeffs == 0];

Reduce[eqs1]


polynomialc2//Factor


(* ::InheritFromParent:: *)
(* (a1 \[Alpha][1]+a1^2 \[Alpha][2]+a2 \[Alpha][3]+a2^2 \[Alpha][4]+b1 \[Alpha][5]+b1^2 \[Alpha][6]+b2 \[Alpha][7]+b2^2 \[Alpha][8]+a1 a2 \[Alpha][9]+a1 b1 \[Alpha][10]+a1 b2 \[Alpha][11]+a2 b1 \[Alpha][12]+a2 b2 \[Alpha][13]+b1 b2 \[Alpha][14])*)


targetpolynomialc2//Factor
