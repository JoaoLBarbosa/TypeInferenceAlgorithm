%:- closure_flag(on).
%:- list_flag(on).


transpose(A,B):-(nullrows(C),C=D),A=D,B=[];((makerow(E,F,G),E=H,F=I,G=J),transpose(K,L),K=J,L=M),A=H,B=[I|M].

makerow(N,O,P):-N=[],O=[],P=[];(makerow(Q,R,S),Q=T,R=U,S=V),N=[[W|X]|T],O=[W|U],P=[X|V].

nullrows(Y):-Y=[];(nullrows(Z),Z=BA),Y=[[]|BA].
