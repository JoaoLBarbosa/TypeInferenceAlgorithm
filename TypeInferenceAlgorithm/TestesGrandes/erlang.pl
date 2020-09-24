%:- closure_flag(on).
%:- list_flag(on).
%:- type(tnam(search_tree,[tvar(-2)]),[func(empty,[]),func(branch,[num,tvar(-2),tnam(search_tree,[tvar(-2)]),tnam(search_tree,[tvar(-2)])])]).

new(A) :- A=empty.

insert(B,C,D,E) :- B=F,C=G,D=empty,E=branch(F,G,empty,empty);((H<I,H=J,I=K),insert(L,M,N,O),L=J,M=P,N=Q,O=R),B=J,C=P,D=branch(K,S,Q,T),E=branch(K,S,R,T);(U==V,U=W,V=X),B=W,C=Y,D=branch(X,Z,BA,BB),E=branch(X,Z,BA,BB);((BC>=BD,BC=BE,BD=BF),insert(BG,BH,BI,BJ),BG=BE,BH=BK,BI=BL,BJ=BM),B=BE,C=BK,D=branch(BF,BN,BO,BL),E=branch(BF,BN,BO,BM).
	
lookup(BP,BQ,BR) :- BP=BS,BQ=empty,BR=error;((BT<BU,BT=BV,BU=BW),lookup(BX,BY,BZ),BX=BV,BY=CA,BZ=CB),BP=BV,BQ=branch(BW,CC,CA,CD),BR=CB;(CE==CF,CE=CG,CF=CH),BP=CG,BQ=branch(CH,CI,CJ,CK),BR=CI;((CL>=CM,CL=CN,CM=CO),lookup(CP,CQ,CR),CP=CN,CQ=CS,CR=CT),BP=CN,BQ=branch(CO,CU,CV,CS),BR=CT.
