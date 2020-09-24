%:- closure_flag(on).
%:- list_flag(on).


literal(A):-A=z0;A=z1;A=z2;A=z3;A=z4;A=z5;A=z6;A=z7;A=z8;A=z9;(literal(B),B=C),A=n(C).

norm(D,E):-(literal(F),F=G),D=G,E=G;((literal(H),H=I),literal(J),J=K),D=o(I,K),E=o(I,K);((literal(L),L=M),literal(N),N=O),D=a(M,O),E=a(M,O);((literal(P),P=Q),norm(R,S),R=T,S=U),D=o(T,Q),E=o(U,Q);(norm(V,W),V=o(o(X,Y),Z),W=BA),D=o(X,o(Y,Z)),E=BA;((norm(BB,BC),BB=BD,BC=BE),norm(BF,BG),BF=a(BH,BI),BG=BJ),D=o(BD,a(BH,BI)),E=o(BE,BJ);((literal(BK),BK=BL),norm(BM,BN),BM=BO,BN=BP),D=a(BO,BL),E=a(BP,BL);(norm(BQ,BR),BQ=a(a(BS,BT),BU),BR=BV),D=a(BS,a(BT,BU)),E=BV;((norm(BW,BX),BW=BY,BX=BZ),norm(CA,CB),CA=o(CC,CD),CB=CE),D=a(BY,o(CC,CD)),E=a(BZ,CE).

dnf(A,B):-(literal(C),C=D),A=D,B=D;((literal(E),E=F),literal(G),G=H),A=o(F,H),B=o(F,H);((literal(I),I=J),literal(K),K=L),A=a(J,L),B=a(J,L);(dnf(M,N),M=O,N=P),A=n(n(O)),B=P;(dnf(Q,R),Q=a(n(S),n(T)),R=U),A=n(o(S,T)),B=U;(dnf(V,W),V=o(n(X),n(Y)),W=Z),A=n(a(X,Y)),B=Z;((dnf(BA,BB),BA=BC,BB=BD),(dnf(BE,BF),BE=BG,BF=BH),norm(BI,BJ),BI=o(BD,BH),BJ=BK),A=o(BC,BG),B=BK;((literal(BL),BL=BM),dnf(BN,BO),BN=BP,BO=a(BQ,BR)),A=a(BP,BM),B=a(a(BQ,BR),BM);((literal(BS),BS=BT),dnf(BU,BV),BU=BW,BV=a(BX,BY)),A=a(BT,BW),B=a(a(BX,BY),BT);((dnf(BZ,CA),BZ=CB,CA=a(CC,CD)),(dnf(CE,CF),CE=CG,CF=a(CH,CI)),norm(CJ,CK),CJ=a(a(CC,CD),a(CH,CI)),CK=CL),A=a(CB,CG),B=CL;((dnf(CM,CN),CM=CO,CN=o(CP,CQ)),(dnf(CR,CS),CR=CT,CS=CU),dnf(CV,CW),CV=o(a(CP,CU),a(CQ,CU)),CW=CX),A=a(CO,CT),B=CX;((dnf(CY,CZ),CY=DA,CZ=DB),(dnf(DC,DD),DC=DE,DD=o(DF,DG)),dnf(DH,DI),DH=o(a(DB,DF),a(DB,DG)),DI=DJ),A=a(DA,DE),B=DJ.

ex:-dnf(DK,DL),DK=DM,DL=a(z1,o(z2,z3)).