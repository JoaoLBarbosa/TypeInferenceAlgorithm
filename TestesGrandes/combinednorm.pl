%:- closure_flag(on).
%:- list_flag(on).


p(A):-A=[B];((p(C),C=[D,E|F]),p(G),G=[s(s(s(s(E))))|F]),A=[s(s(D)),E|F];(p(H),H=I),A=[0|I].

transpose(J,K):-(transposeaux(L,M,N),L=O,M=[],N=P),J=O,K=P.

transposeaux(Q,R,S):-((row2col(T,U,V,W,X),T=Y,U=[Z|BA],V=BB,W=[],X=BC),transposeaux(BD,BE,BF),BD=BG,BE=BC,BF=BB),Q=[Y|BG],R=BH,S=[Z|BA];Q=[],R=BI,S=BI.

row2col(BJ,BK,BL,BM,BN):-(row2col(BO,BP,BQ,BR,BS),BO=BT,BP=BU,BQ=BV,BR=[[]|BW],BS=BX),BJ=[BY|BT],BK=[[BY|BZ]|BU],BL=[BZ|BV],BM=BW,BN=BX;BJ=[],BK=[],BL=[],BM=CA,BN=CA.
	
parse(CB,CC):-((app(CD,CE,CF),CD=CG,CE=[a,s(CH,CI,CJ),b|CK],CF=CL),(app(CM,CN,CO),CM=CG,CN=[s(a,s(CH,CI,CJ),b)|CK],CO=CP),parse(CQ,CR),CQ=CP,CR=CS),CB=CL,CC=CS;((app(CT,CU,CV),CT=CW,CU=[a,s(CX,CY),b|CZ],CV=DA),(app(DB,DC,DD),DB=CW,DC=[s(a,s(CX,CY),b)|CZ],DD=DE),parse(DF,DG),DF=DE,DG=DH),CB=DA,CC=DH;((app(DI,DJ,DK),DI=DL,DJ=[a,b|DM],DK=DN),(app(DO,DP,DQ),DO=DL,DP=[s(a,b)|DM],DQ=DR),parse(DS,DT),DS=DR,DT=DU),CB=DN,CC=DU;CB=[s(DV,DW)],CC=s(DV,DW);CB=[s(DX,DY,DZ)],CC=s(DX,DY,DZ).

app(A,B,C):-A=[],B=D,C=D;(app(E,F,G),E=H,F=I,G=J),A=[K|H],B=I,C=[K|J].

ackermann(EA,EB,EC):-EA=0,EB=ED,EC=s(ED);(ackermann(EE,EF,EG),EE=EH,EF=s(0),EG=EI),EA=s(EH),EB=0,EC=EI;((ackermann(EJ,EK,EL),EJ=s(EM),EK=EN,EL=EO),ackermann(EP,EQ,ER),EP=EM,EQ=EO,ER=ES),EA=s(EM),EB=s(EN),EC=ES.
