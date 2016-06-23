n := 2^GetSeed();
p:=n^2; 
r:=n;
gamma:=2*n;
L:=8;
gz:=n^2;
g:=n^2 div L;

m:=2*gamma;
leb:=n;  //length of the element in the base (at the pre-computation stage) in terms of the element already found as a product of the gen'
cpu_bound:=70;

/* of Attack */
g1:=3;

/* STRUCTURES */

S:=SymmetricGroup(n);
Alt:=AlternatingGroup(n);
B:=BraidGroup(n);
SetPresentation(~B,"Artin");
D:=FundamentalElement(B);
SetElementPrintFormat(~B,"Word");

F:=GF(p);
T:=[];
for i:=1 to n do
  T[i]:="t" cat IntegerToString(i);
end for; 
R:=FunctionField(F,n); 
AssignNames(~R,T); 
M:=MatrixAlgebra(R,n); 
G:=GL(n,R); 
MF:=MatrixAlgebra(F,n);


/* FUNCTIONS */


function vec(A,m)     //Conversion of matrix to a vector
   T:=[ Transpose(A)[i] : i in [1..m] ];
   return Vector(HorizontalJoin(T));
end function;

function revers_vec(v,m,F)      //Conversion of vector to amatrix
	A:= ZeroMatrix(F,m,m);
       for j:=1 to m do
	     for i:=1 to m do
    	    A[j,i] := v[(i-1)*m+j];
	     end for;
	end for;
	return A;
end function;


function random_sp_seq(vv,seq,F)   //given a span{}, finding an invertible elemnt there    
	ki:=revers_vec(vv!0,n,F);
	while not IsInvertible(ki) do     
		ki:=vv!0;
		for s in seq do   
		   ki +:= Random([0..1])*Random([1..20])*s;
		end for;
		ki:=revers_vec(ki,n,F);
	end while;
	return ki;
end function;

function RandomPositiveWord(n,l)

RndAL:=[];
for i:=1 to l do
  Append(~RndAL,Random(1,n-1));
end for;
br:=B!RndAL;
return br;
end function;


function EvaluateMat(Mat,varind,var0)
EM:=Id(M);
for i:=1 to n do
  for j:=1 to n do
    EM[i,j]:=Evaluate(Mat[i,j],varind,var0);
  end for; 
end for;
return EM;
end function; 

function  EvaluateMultivariateMat(Mat,Tau)

EMM:=Mat;
for i:=1 to n do
  EMM:=EvaluateMat(EMM,i,Tau[i]);
end for;
return EMM;
end function;

function ColoredBurauMatrix(b)

CBM:=Id(M);
wb:=Eltseq(b);
w:=[]; 
bw:=B!1;
for i:=1 to #wb do
  j:=Abs(wb[i]);
  if Sign(wb[i]) eq 1 then
    s:=Eltseq(InducedPermutation(bw)^-1); 
    y:=Id(M);
    if j eq 1 then
      y[1,1]:=-R.(s[j]);
      y[1,2]:=1;
    else
      y[j,j-1]:=R.(s[j]);
      y[j,j]:=-R.(s[j]);
      y[j,j+1]:=1;
    end if;
  else
    s:=Eltseq((InducedPermutation(bw)*S!(j,j+1))^-1); 
    y:=Id(M);
    if j eq 1 then
      y[1,1]:=-R.(s[j]);
      y[1,2]:=1;
    else
      y[j,j-1]:=R.(s[j]);
      y[j,j]:=-R.(s[j]);
      y[j,j+1]:=1;
    end if;  
  end if;  
  CBM:=CBM*(y^(Sign(wb[i])));
  Append(~w,wb[i]);
  bw:=B!w;
end for;
return CBM;
end function;



function effEvaluateCBM(s, b,Tau)
"Computing", s, "...", Cputime();
wb:=Eltseq(b);
CBM:=Id(M);
ECBM:=EvaluateMultivariateMat(CBM,Tau);
w:=[]; 
bw:=B!1;
for i:=1 to #wb do
  j:=Abs(wb[i]);
  if Sign(wb[i]) eq 1 then
    s:=Eltseq(InducedPermutation(bw)^-1); 
    y:=Id(M);
    if j eq 1 then
      y[1,1]:=-R.(s[j]);
      y[1,2]:=1;
    else
      y[j,j-1]:=R.(s[j]);
      y[j,j]:=-R.(s[j]);
      y[j,j+1]:=1;
    end if;
  else
    s:=Eltseq((InducedPermutation(bw)*S!(j,j+1))^-1); 
    y:=Id(M);
    if j eq 1 then
      y[1,1]:=-R.(s[j]);
      y[1,2]:=1;
    else
      y[j,j-1]:=R.(s[j]);
      y[j,j]:=-R.(s[j]);
      y[j,j+1]:=1;
    end if;  
  end if;
  Ey:=EvaluateMultivariateMat(y,Tau);  
  ECBM:=ECBM*(Ey^(Sign(wb[i])));
  Append(~w,wb[i]);
  bw:=B!w;
end for;
"... done", Cputime();
return ECBM;
end function;



function RandomLowerBraidWord(L)

w:=[];
s:=Random(0,1);
a:=Random(1,(n div 2)-1);
if s eq 1 then 
     w[1]:=a;
else w[1]:=-a;
end if;
for i:=2 to L do
  repeat
    s:=Random(0,1);
    a:=Random(1,(n div 2)-1);
    if s eq 1 then 
         w[i]:=a;
    else w[i]:=-a;
    end if;
  until w[i] ne -w[i-1];
end for;
b:=B!w; 
return b;
end function;


function RandomUpperBraidWord(L)

w:=[];
s:=Random(0,1);
a:=Random((n div 2)+1,n-1);
if s eq 1 then 
     w[1]:=a;
else w[1]:=-a;
end if;
for i:=2 to L do
  repeat
    s:=Random(0,1);
    a:=Random((n div 2)+1,n-1);
    if s eq 1 then 
         w[i]:=a;
    else w[i]:=-a;
    end if;
  until w[i] ne -w[i-1];
end for;
b:=B!w; 
return b;
end function;


/* STEPS of Algebraic Eraser Protocol as FUNCTIONs */ 

function Generate_m0()
repeat 
  m0:=Random(MF); 
until IsInvertible(m0) and Order(m0) eq p^n -1;
return m0;
end function;


function Generate_Matrixn_in_N(m0) /* N_A=N_B */
repeat
  nA:=MF!0; 
  for i:=1 to r do
    repeat 
      lA:=Random(F); 
    until lA ne 0;  
    kA:=Random(1,Order(m0)-1); 
    nA:=nA+lA*m0^kA;
  end for;
until IsInvertible(nA);
return nA;
end function;


function Construct_Generators_of_A(z)
V:=[];
for i:=1 to gamma do
  V[i]:=RandomLowerBraidWord(L);
  V[i]:=z*V[i]*z^-1;
  LeftNormalForm(~V[i]);
  Tv:=CFP(V[i]); 
  if (Tv[2] mod 2) eq 0 then
    Tv[2]:=0;
  else Tv[2]:=1;
  end if;
  V[i]:=B!Tv;
end for;
return V;
end function;


function Construct_Generators_of_B(z) 
W:=[];
for i:=1 to gamma do
  W[i]:=RandomUpperBraidWord(L);
  W[i]:=z*W[i]*z^-1;
  LeftNormalForm(~W[i]);
  Tw:=CFP(W[i]);
  if (Tw[2] mod 2) eq 0 then
    Tw[2]:=0;
  else Tw[2]:=1;
  end if;
  W[i]:=B!Tw;
end for;
return W;
end function;


function InducedPermutation_of_Generators(W) 
sW:=[];
for i:=1 to gamma do
  sW[i]:=InducedPermutation(W[i]);
end for;
return sW;
end function;



function Generate_Elt_in_A(V,g)
s:=Random(0,1);
abs:=Random(1,gamma);
if s eq 1 then 
     a:=V[abs];
else a:=V[abs]^-1;
end if;
for i:=2 to g do
  absOld:=abs; sOld:=s; 
  repeat 
    s:=Random(0,1);
    abs:=Random(1,gamma);
  until abs ne absOld or s eq sOld;
  if s eq 1 then 
       a1:=V[abs];
  else a1:=V[abs]^-1;
  end if;
  a:=a*a1;
end for;
return(a);
end function;


function Generate_Elt_in_B(W)
s:=Random(0,1);
abs:=Random(1,gamma);
if s eq 1 then 
     b:=W[abs];
else b:=W[abs]^-1;
end if;
for i:=2 to g do
  absOld:=abs; sOld:=s; 
  repeat 
    s:=Random(0,1);
    abs:=Random(1,gamma);
  until abs ne absOld or s eq sOld;
  if s eq 1 then 
       b1:=W[abs];
  else b1:=W[abs]^-1;
  end if;
  b:=b*b1;
end for;
return(b);
end function;


function Generate_Tau()
Tau:=[];
for i:=1 to n do
  rand:=0;
  repeat
    rand:=Random(F);
  until rand ne 0;
  Tau[i]:=rand;
end for;
return Tau;
end function;


function PermAction_on_Tau(s,Tau)
sTau:=[];
for i:=1 to n do
  sTau[i]:=Tau[Eltseq(s^-1)[i]];
end for;
return sTau;
end function;


/* FUNCTIONS used in ATTACK */


function Generate_bt_Bt_saBt(K,Tau,saTau,W)
bt:=[]; Bt:=[]; saBt:=[];
for j:=1 to K do
  repeat
    bt[j]:=Id(B);
    for i:=1 to g1 do
      rd:=Random(0,1);
      abs:=Random(1,gamma);
      if rd eq 1 then 
          b1:=W[abs];
      else b1:=W[abs]^-1;
      end if;
      bt[j]:=bt[j]*b1;
    end for;
    o:=Order(InducedPermutation(bt[j]));
  until o le n;
  bt[j]:=bt[j]^o;
  Bt[j]:=MF!(effEvaluateCBM("bt[j]", bt[j],Tau));
  saBt[j]:=MF!(effEvaluateCBM("bt[j]", bt[j],saTau));
end for;
return bt,Bt,saBt;
end function;

function Kernel_of_reconstrA(K,nBt,Bt,saBt,pA)
T:=[];
for i:=1 to K do
  T[i]:=KroneckerProduct(Id(MF),Transpose(saBt[i])) -
        KroneckerProduct(Bt[i],Id(MF));
end for;
T[K+1]:=KroneckerProduct(Id(MF),Transpose((pA^-1)*nBt)) -
        KroneckerProduct(nBt,Transpose((pA^-1)));
T0:=VerticalJoin(T);
Kern:=NullspaceOfTranspose(T0);
return Kern;
end function;

function Onedim_Kernel_of_reconstrA(nBt,Tau,saTau,W,pA)
T:=[];
k:=0;
repeat
"Try number:", k;
  k:=k+1;
  bt,Bt,saBt:=Generate_bt_Bt_saBt(k,Tau,saTau,W);
  for i:=1 to k do
    T[i]:=KroneckerProduct(Id(MF),Transpose(saBt[i])) -
          KroneckerProduct(Bt[i],Id(MF));
  end for;
  T[k+1]:=KroneckerProduct(Id(MF),Transpose((pA^-1)*nBt)) -
          KroneckerProduct(nBt,Transpose((pA^-1)));
  T0:=VerticalJoin(T);
  Kern:=NullspaceOfTranspose(T0);
"Dim:", Dimension(Kern);
until Dimension(Kern) eq 1;
return Kern;
end function;


function recoveredA(Kern)
GenSet:=Generators(Kern);
GenSeq:=SetToSequence(GenSet);
vecA:=Eltseq(GenSeq[1]);
rA:=MF!1;
for i:=1 to n do
 for j:=1 to n do
   rA[i,j]:=vecA[(i-1)*n+j];
  end for;
end for;
return rA;
end function;

/* FUNCTIONS for STEP 2: Factorization in PermGroup */


function RandomGeneratingSet()
s:=[];
for i:=1 to gamma do
  s[i]:=Random(S);
  s[gamma +i]:=s[i]^-1;
end for; 
return s;
end function;


function GenerateFreeRedWord(k,K,N)
  w:=[];
  q:=Intseq(N,m-1);
  for j:=1 to #q do
    q[j]:=q[j]+1;
  end for;
  for j:=#q +1 to k-1 do 
    q[j]:=1; 
  end for;
  w:=[K] cat q;
  for i:=1 to #w -1 do
    if w[i] le gamma then
      if w[i+1] ge w[i]+gamma then
        w[i+1]:=w[i+1]+1;
      end if;
    else
      if w[i+1] ge w[i]-gamma then
        w[i+1]:=w[i+1]+1;
      end if; 
    end if;      
  end for;
return w;
end function;


function Perm(q,s)
tau:=Id(S);
for j:=1 to #q do   
  tau:=tau*s[q[j]];
end for;
return tau;
end function;


function InvWord(W)
Winv:=Reverse(W);
for i:=1 to #W do
  if W[#W-i+1] le gamma then
       Winv[i]:=W[#W-i+1]+gamma;
  else Winv[i]:=W[#W-i+1]-gamma;
  end if;
end for; 
return Winv;
end function;


function PermAction(q,s,x)
y:=x;
for j:=1 to #q do   
  y:=y^s[q[j]];
end for;
return y;
end function;


procedure Order3c(~cyc)
k:=1;
for i:=2 to 3 do
  if cyc[i] lt cyc[k] then
    k:=i;
  end if;
end for;
if k eq 2 then
  cyc:=[cyc[2],cyc[3],cyc[1]];
end if;
if k eq 3 then
  cyc:=[cyc[3],cyc[1],cyc[2]];
end if;  
end procedure;


procedure Order2c(~cyc)
 if cyc[1] gt cyc[2] then
  cyc:=[cyc[2],cyc[1]];
end if;
end procedure;


procedure FreeReduce(~w)
i:=1;
while i lt #w do
  red:=false;
  if Abs(w[i]-w[i+1]) eq gamma then
    Remove(~w,i);
    Remove(~w,i); 
    red:=true;
    if i ne 1 and i ne #w +1 and Abs(w[i]-w[i-1]) eq gamma then
      i:=i-1; 
    end if;
  end if;
  if red eq false then
    i:=i+1;
  end if;
end while;  
end procedure;


/*  FUNCTIONS: STEPS OF Factorization algorithm */


function STEP_1_further_improvedExperiment(s)
d:=n;
D:=n;
m0:=Maximum(3,n/4);
lambda:=128;
t1:=lambda*n;
t:=0;
L:=1000000;
breakbool:=true;
k:=1;
Ntau1:=0;
while breakbool do
  for K:=1 to m do
    for N:=0 to (m-1)^(k-1)-1 do
         q1:=GenerateFreeRedWord(k,K,N);      
         tau1:=Perm(q1,s);
         Ntau1:=Ntau1+1;
         Ltau1:=#q1;
         canc:=[]; 
         i:=1;
         while Abs(q1[1]-q1[#q1]) eq gamma do
           canc[i]:=q1[1];
           Remove(~q1,#q1);
           Remove(~q1,1);
           i:=i+1;
         end while;
         q0i:=[]; q1i:=[];
         for i:=1 to d do
           q0i:=q0i cat q1;  
           q1i:=canc cat q0i cat InvWord(canc); 
           tau1i:=tau1^i;
           Dtau1i:=Degree(tau1i);
           if (Dtau1i lt D and tau1i ne Id(S)) or
           (Dtau1i eq D 
           and #q1i lt L 
           and tau1i ne Id(S)) then
             tau:=tau1i;
             Ntau1act:=Ntau1;
             Ltau1act:=Ltau1;
             iact:=i;
             D:=Degree(tau);
             W:=q1i;
             L:=#W;
           end if;                    
         end for;
         t:=t+1;
         if t gt t1 and D le m0 then
           breakbool:=false;
           break K;
         end if;  
    end for;
  end for;
  k:=k+1;
end while;
return tau,W,Ntau1act,iact,Ltau1act;
end function;


function STEP_2Experiment(tau,W,s)
timing:= Cputime();
TotNpi:=0;
NRedDegtau:=0;
repeat
  NRedDegtau:=NRedDegtau+1;
  breakbool:=true;
  k:=1; 
  while breakbool do
     for K:=1 to m do
       for N:=0 to (m-1)^(k-1)-1 do
         Wpi:=GenerateFreeRedWord(k,K,N); 
         pi:=Perm(Wpi,s);   
         TotNpi:=TotNpi+1;     
         nset:={1..n}; 
         A:=nset diff Fix(tau);
         Api:={};
         for x in A do 
           Include(~Api,x^(pi));
         end for;
         M:=A meet Api;
       
         x1found:=false;  
         for x1 in A do 
           u1:=x1^(pi);
           u2:=u1^(tau);
           x2:=u2^(pi^-1);
           if u1 in A and x2 notin A then 
             x1found:=true;
             break;
           end if; 
         end for;
       
         if #M le 1+(#A)^2/n and x1found then
           tau:=(tau^-1)*((tau^pi)^-1)*tau*tau^pi;
           Winv:=InvWord(W);
           Wtp:=InvWord(Wpi) cat W cat Wpi;
           Wtpinv:=InvWord(Wpi) cat Winv cat Wpi;
           W:=Winv cat Wtpinv cat W cat Wtp;
           breakbool:=false;
           break;
         end if;  
       end for;       
     end for;
     k:=k+1;
	 //if Cputime(timing) ge cpu_bound then break;
	 //end if;
  end while;
until Degree(tau) eq 3 or Degree(tau) eq 2 or (Cputime(timing) ge cpu_bound);

//if Cputime(timing) ge cpu_bound then 
	//return 0,tau,W,NRedDegtau,TotNpi;
//else
	return 1,tau,W,NRedDegtau,TotNpi;
//end if;
end function;




function STEP_3_3cycles_improvedExp(tau,W,s,c3d)
cd:=CycleDecomposition(tau); 
for i:=1 to #cd do
  if #cd[i] gt 1 then
    t1:=cd[i][1];
    t2:=cd[i][2];
    t3:=cd[i][3];
    break;
  end if;
end for;
t:=[t1,t2,t3];

C3:={}; c3:=[];
full:=#c3d;
if t in c3d then
  Include(~C3,t);
  Append(~c3,<t,W>);
end if;

breakbool:=true;
k:=1; 
NWpiStep33:=0;
timing:= Cputime();
while breakbool do 
  for K:=1 to m do
    for N:=0 to (m-1)^(k-1)-1 do
        Wpi:=GenerateFreeRedWord(k,K,N);
        NWpiStep33:=NWpiStep33+1; 
        tp:=[PermAction(Wpi,s,t1),PermAction(Wpi,s,t2),PermAction(Wpi,s,t3)];
        Order3c(~tp);
        if tp notin C3 and tp in c3d then
          Include(~C3,tp); 
          W1:=InvWord(Wpi) cat W cat Wpi; 
          Append(~c3,<tp,W1>);
          if #C3 eq full then
            breakbool:=false;
            break;
          end if;
        end if;    
    end for;
  end for;
  k:=k+1;
  //if Cputime(timing) ge cpu_bound then break;
  //end if;
end while;

//if Cputime(timing) ge cpu_bound then 
	//return 0,c3,NWpiStep33;
//else
	return 1,c3,NWpiStep33;
//end if;
end function;


function STEP_41_3cycles(p)
Cd:=CycleDecomposition(p);
c:=[];c2d:=[];
for i:=1 to #Cd do
  c[i]:=Setseq(Cd[i]);
  for j:=#c[i] to 2 by -1 do
    Append(~c2d,[c[i][j],c[i][j-1]]);
  end for;
end for;

c3d:=[];
for i:=2 to #c2d by 2 do
  if c2d[i-1][2] eq c2d[i][1] then
       a:=[c2d[i-1][1],c2d[i][2],c2d[i][1]];
       Order3c(~a);
       Append(~c3d,a);
  else a:=[c2d[i-1][1],c2d[i][1],c2d[i-1][2]];
       Order3c(~a);
       Append(~c3d,a);
       a:=[c2d[i][1],c2d[i-1][2],c2d[i][2]];
       Order3c(~a);
       Append(~c3d,a);
  end if;
end for;
return c3d;
end function;

function STEP_42_3cycles(c3,c3d)
Wresult:=[];
for i:=1 to #c3d do
  for j:=1 to #c3 do
    if c3[j][1] eq c3d[i] then
      Wresult:=Wresult cat c3[j][2];
    end if;
  end for;
end for;
return Wresult;
end function;


function STEP_3_2cycles_improvedExp(tau,W,s,c2d)

cd:=CycleDecomposition(tau); 
for i:=1 to #cd do
  if #cd[i] gt 1 then
    t1:=cd[i][1];
    t2:=cd[i][2];
    break;
  end if;
end for;
t:=[t1,t2];

C2:={};c2:=[];
full:=#c2d; 
if t in c2d then
  Include(~C2,t);
  Append(~c2,<t,W>);
end if;
breakbool:=true;
k:=1; 
NWpiStep32:=0;
timing:=Cputime();
while breakbool do
  for K:=1 to m do
    for N:=0 to (m-1)^(k-1)-1 do 
      Wpi:=GenerateFreeRedWord(k,K,N);
      NWpiStep32:=NWpiStep32+1; 
        tp:=[PermAction(Wpi,s,t1),PermAction(Wpi,s,t2)];
        Order2c(~tp);
        if tp notin C2 and tp in c2d then
          Include(~C2,tp); 
          W1:=InvWord(Wpi) cat W cat Wpi; 
          Append(~c2,<tp,W1>);
          if #C2 eq full then
            breakbool:=false;
            break;
          end if;
        end if;     
    end for;
  end for;
  k:=k+1;
 // if Cputime(timing) ge cpu_bound then break;
 // end if;
end while;
//if Cputime(timing) ge cpu_bound then
//	return 0,c2,NWpiStep32;
//else
	return 1,c2,NWpiStep32;
//end if;
end function;


function STEP_41_2cycles(p) 

Cd:=CycleDecomposition(p);

c:=[];c2d:=[];
for i:=1 to #Cd do
  c[i]:=Setseq(Cd[i]);
  for j:=#c[i] to 2 by -1 do
    a:=[c[i][j],c[i][j-1]];
    Order2c(~a);
    Append(~c2d,a);
  end for;
end for;
return c2d;
end function;

function STEP_42_2cycles(c2,c2d)
Wresult:=[];
for i:=1 to #c2d do
  for j:=1 to #c2 do
    if c2[j][1] eq c2d[i] then
      Wresult:=Wresult cat c2[j][2];
    end if;
  end for;
end for;
return Wresult;
end function;

function GenerateOddPerm(s)

breakbool:=true;
k:=1;
while breakbool do
  for K:=1 to m do
    for N:=0 to (m-1)^(k-1)-1 do 
      q:=GenerateFreeRedWord(k,K,N);
      pe:=Perm(q,s); 
      if IsOdd(pe) then
         breakbool:=false;
         break;
      end if;
    end for;
  end for;
  k:=k+1;
end while;
return pe,q;
end function;


function braid_to_array(b,B)
	t_ar_b:=Eltseq(b);
	ar_b:=[];
	for i:= 1 to #t_ar_b do
		if t_ar_b[i] ge 0 then 
			Append(~ar_b, t_ar_b[i]);
			Append(~ar_b, 1);
		else
			Append(~ar_b, -t_ar_b[i]);
			Append(~ar_b, -1);
		end if;
	end for;
	Insert(~ar_b, 1, #t_ar_b);
	return ar_b;
end function;

function inv_Wi(i,W,W_num)
	Wi_array:=braid_to_array(W[W_num[i]],B);
	temp:=Reverse(Wi_array);
	rev_W_array:=[];
	for j:= 1 to (#temp div 2) do
		Append(~rev_W_array, temp[2*j]);
		Append(~rev_W_array, -temp[2*j-1]);
	end for;
	return rev_W_array;
end function;

function compute_phi_br_tau(inpurt_array,MF,S,cur_tau)       //br is the braid at the inpurtfile
	temp:=inpurt_array;
	result:=Id(MF);
	temp_per:=Id(S);
		for i:= 1 to temp[1] do
			if (i mod 100) eq 0 then
				"i";i; "GetMemoryUsage()";GetMemoryUsage();
			end if;
			act_tau:=PermAction_on_Tau(temp_per,cur_tau);
			result:=result*effEvaluateCBM("result",(B.temp[2*i])^temp[2*i+1],act_tau);
			temp_per:=temp_per*InducedPermutation((B.temp[2*i])^temp[2*i+1]);
		end for;
	return result;
end function;


function Generate_Elt_in_B_try1(W)
//s:=Random(0,1);
abs:=Random(1,gamma);
w_num:=[abs];
//if s eq 1 then 
     b:=W[abs];
//else b:=W[abs]^-1;
//end if;
for i:=2 to g do
//  absOld:=abs; sOld:=s; 
//  repeat 
//    s:=Random(0,1);
    abs:=Random(1,gamma);
	Append(~w_num,abs);
//  until abs ne absOld or s eq sOld;
//  if s eq 1 then 
       b1:=W[abs];
//  else b1:=W[abs]^-1;
//  end if;
  b:=b*b1;
end for;
return b, w_num;
end function;


/* ---------------------------- */

 /* MAIN FUNCTION used */

function FactorizationPermWithoutSTEP1(p,s,tau,W)
NRedDegtau:=0;
TotNpi:=0;
NWpiStep33:=0;
NWpiStep32:=0;
if Degree(tau) gt 3 then
  get_01,tau,W,NRedDegtau,TotNpi:=STEP_2Experiment(tau,W,s);
  c3d:=STEP_41_3cycles(p);
  get_01,c3,NWpiStep33:=STEP_3_3cycles_improvedExp(tau,W,s,c3d);
  Wres:=STEP_42_3cycles(c3,c3d);
elif Degree(tau) eq 3 then
  c3d:=STEP_41_3cycles(p); 
  get_01,c3,NWpiStep33:=STEP_3_3cycles_improvedExp(tau,W,s,c3d);
  Wres:=STEP_42_3cycles(c3,c3d);
else
  c2d:=STEP_41_2cycles(p); 
  get_01,c2,NWpiStep32:=STEP_3_2cycles_improvedExp(tau,W,s,c2d);
  Wres:=STEP_42_2cycles(c2,c2d);
end if;

if get_01 eq 0 then
	return 0,Wres,NRedDegtau,TotNpi,NWpiStep33,NWpiStep32;
else 
	return 1,Wres,NRedDegtau,TotNpi,NWpiStep33,NWpiStep32;
end if;
end function;


/* _________________________________________________________________________________ */


/* private key generation */

"Generating private keys...";
//m0:=Generate_m0();
//nA:=Generate_Matrixn_in_N(m0);
//nB:=Generate_Matrixn_in_N(m0);
z:=RandomWord(B,gz,gz);
V:=Construct_Generators_of_A(z);
W:=Construct_Generators_of_B(z);
a:=Generate_Elt_in_A(V,g);
b:=Generate_Elt_in_B(W);

Tau:=Generate_Tau();
ar_W1:= braid_to_array(W[1],B);
pi_betta:=compute_phi_br_tau(ar_W1,MF,S,Tau);                      
repeat
  m0:=Random(F)*MF!1;
  for i:=1 to r do                               //instead of "m0:=Generate_m0();"
    m0:=pi_betta*m0+Random(F)*MF!1;
  end for;
until IsInvertible(m0);
m0:=MF!m0;

nA:=Generate_Matrixn_in_N(m0);
nB:=Generate_Matrixn_in_N(m0);


"...done.";

/* Public */

"Public stuff..."; 
//Tau:=Generate_Tau();

/* to be recovered */

/* Pi(A) */
ar_a:=braid_to_array(a,B);

"Computing A0...";
A0:=compute_phi_br_tau(ar_a,MF,S,Tau); 
"done.";

/* Pi(B) */
ar_b:=braid_to_array(b,B);

"Computing B0...";
B0:=compute_phi_br_tau(ar_b,MF,S,Tau); 
"done.";


/* Public keys */

pA:=MF!(nA*A0); 
sa:=InducedPermutation(a);
pB:=MF!(nB*B0); 
sb:=InducedPermutation(b);

saTau:=PermAction_on_Tau(sa,Tau);
sbTau:=PermAction_on_Tau(sb,Tau);
"...done";

/* further to be recovered */

"Further to be recovered...";

"Computing sbA...";
sbA:=compute_phi_br_tau(ar_a,MF,S,sbTau);
"...done";

"Computing saB...";
saB:=compute_phi_br_tau(ar_b,MF,S,saTau);
"...done";

/* Shared Keys */

KA:=nA*pB*sbA;
KB:=nB*pA*saB;  
"...done";

/* ATTACK */

/* -----------  precomputation stage ---------- */
/*=====================================================================*/
//Generate a short product, (b_tag, g_tag) , of generators of B. 
phi_beta:=[];

counter_stop_dim:=0;
prev_dim:=0;
VV:= VectorSpace(F, n^2);
base_phi:=[MF|];
v_base_phi:=[VV|];
base_for_betta1:=[MF|];
mm:=[MF|];
stepcount := 0;
repeat 
	stepcount +:= 1;
    "Step:", stepcount;
	
	order_g_tag:=2*n;
	while order_g_tag ge (n) do
		b_tag,W_num:=Generate_Elt_in_B_try1(W);
		g_tag:= InducedPermutation(b_tag);
		order_g_tag:= Order(g_tag);
	end while;	

	
	array_b_tag:=braid_to_array(W[W_num[1]],B);
	Remove(~array_b_tag,1);
	for i:=2 to g do
		temp_array:=braid_to_array(W[W_num[i]],B);
		Remove(~temp_array,1);
		Insert(~array_b_tag,#array_b_tag+1,#array_b_tag+1,temp_array);
	end for;
	Insert(~array_b_tag, 1, #array_b_tag div 2);
	
	//check
	check:=Id(B);
	for i:= 1 to (#array_b_tag div 2) do
		check:=check*(B.(array_b_tag[2*i]))^(array_b_tag[2*i+1]);
	end for;
	"check eq b_tag"; check eq b_tag;
	
/* -----------  Express g'' as word in sw[1],..,sw[gamma] ---------- */

	/* Preparation */
	g_2tag:= g_tag^-1;
	b_2tag:=Id(B);
	

	cc:=compute_phi_br_tau(array_b_tag,MF,S,Tau);
	cc_beta:=compute_phi_br_tau(array_b_tag,MF,S,saTau);
	corent_tau:= Tau;
	"order_g_tag"; order_g_tag;
	for i:=2 to (order_g_tag) do
		"iteration number"; i;
		corent_tau:=PermAction_on_Tau(g_tag,corent_tau);
		corent_tau_for_beta:=PermAction_on_Tau(sa,corent_tau);
		cc:= cc*compute_phi_br_tau(array_b_tag,MF,S,corent_tau);
		cc_beta:=cc_beta*compute_phi_br_tau(array_b_tag,MF,S,corent_tau_for_beta);
	end for;

	
	//if InducedPermutation(cc) eq g_tag^order_g_tag 
	//	then print "CORRECT permutation";
		
		cc_in_mm:= MF!cc in mm;
		print "cc_in_mm", MF!cc in mm;
				
		if not cc_in_mm then
			VV:= VectorSpace(F, n^2);
			Append(~base_phi,MF!cc);
			Append(~v_base_phi,VV!vec(cc,n));
			//g_tag_sa_Tau1:=PermAction_on_Tau(g_tag*sa,Tau);
			Append(~base_for_betta1,MF!cc_beta);
			mm:=MatrixAlgebra<F,n|base_phi>;
			dim_mm:=Dimension(mm);
		end if;
		if dim_mm eq prev_dim then 
			counter_stop_dim:=counter_stop_dim+1;
		end if;
		prev_dim:=dim_mm;
	
	//end if;

until (counter_stop_dim ge 4);

final_v_base_phi:=v_base_phi;
final_base_phi:=base_phi;
V_article:=sub<VV|final_v_base_phi>;
final_base_for_betta1:=base_for_betta1;


repeat
	new_cc:=Id(MF);
	new_cc_beta:=Id(MF);
	ll:=Random([1..leb]);
	for i:= 1 to ll do
		corent_el:=Random([1..#base_phi]);
		new_cc:=new_cc*base_phi[corent_el];
		new_cc_beta:=new_cc_beta*base_for_betta1[corent_el];
		bool_depended:=VV!vec(new_cc,n) in V_article;
	end for;
	if not bool_depended then
		//counter_dim_v:=counter_dim_v+1;
		Append(~final_v_base_phi,VV!vec(new_cc,n));
		Append(~final_base_phi,MF!new_cc);
		V_article:=sub<VV|final_v_base_phi>;
		print "Dimension(V_article)", Dimension(V_article) ;
		Append(~final_base_for_betta1,MF!new_cc_beta);
		
	end if;
until (Dimension(V_article) eq Dimension(mm));
 
    
                          
/* -----------  stage 1 ---------- */
/* ======================================== */



/* Express sb (in our notation - p) as word in sw[1],..,sw[gamma] */


/* Preparation */
sW:=InducedPermutation_of_Generators(W);
H:=sub<S|sW>;
ind:=Index(S,H);
print "Index(S,H)",Index(S,H);
print "Order(H)=",Order(H);
print "sb in H",sb in H;
for i:=1 to gamma do
  sW[i+gamma]:=sW[i]^-1;
end for;

/* Main */
repeat
  tau,Wtau,Ntau1act,iact,Ltau1act:=STEP_1_further_improvedExperiment(sW);
  print "Deg(tau)=",Degree(tau);
  print "suff. Number of chosen tau1=",Ntau1act;
  print "power of tau1=iact=",iact;
  print "Length(tau1)=",Ltau1act;
  print "Length(tau)=#Wtau=",#Wtau;
  if (ind eq 1) and IsOdd(p) and Degree(tau) eq 3 then
    print "CRITICAL CASE:";
    pe,peW:=GenerateOddPerm(sW);
    Evenp:=pe*sb;   
    get_0_1,EvenpW,NRedDegtau,TotNpi,NWpiStep33,NWpiStep32:=FactorizationPermWithoutSTEP1(Evenp,sW,tau,Wtau);
    Wres:=InvWord(peW) cat EvenpW;
  else get_0_1,Wres,NRedDegtau,TotNpi,NWpiStep33,NWpiStep32:=FactorizationPermWithoutSTEP1(sb,sW,tau,Wtau);
  end if;
  
  if get_0_1 eq 1 then
	  print "NRedDegtau,TotNpi=",NRedDegtau,",",TotNpi;
	  print "NWpiStep33=",NWpiStep33;
	  print "NWpiStep32=",NWpiStep32;
	  print "#Wres=",#Wres;
	  FreeReduce(~Wres);
	  print "#Wresfreered=",#Wres;
	  if Perm(Wres,sW) eq sb then 
		print "success"; 
	  end if;

	  
		arrayW_b_tilde:=[];
		b_tilde:=Id(B);
		for i:=1 to #Wres do
		  if Wres[i] le gamma then
				Append(~arrayW_b_tilde, Wres[i]);
				Append(~arrayW_b_tilde, 1);
			    b_tilde:=b_tilde*W[Wres[i]];
		  else 
				Append(~arrayW_b_tilde, Wres[i]-gamma);
				Append(~arrayW_b_tilde, -1);
				b_tilde:=b_tilde*W[Wres[i]-gamma]^-1;
		  end if;
		end for;
		
		"#Wres of b_tilde"; #Wres;
		"#arrayW_b_tilde"; #arrayW_b_tilde;
		

		if InducedPermutation(b_tilde) eq sb then
			print "CORRECT permutation";	
			
			array_b_tilde:=[];
			for i:=1 to (#arrayW_b_tilde div 2) do
				if arrayW_b_tilde[2*i] eq 1 then
					temp_array:=braid_to_array(W[arrayW_b_tilde[2*i-1]],B);
					Remove(~temp_array,1);
				else 
					temp_array:=inv_Wi(2*i-1,W,arrayW_b_tilde);
					//Remove(~temp_array,1);
				end if;
				Insert(~array_b_tilde,#array_b_tilde+1,#array_b_tilde+1,temp_array);
			end for;
			
			Insert(~array_b_tilde,1, #array_b_tilde div 2);
			
			#array_b_tilde div 2;
			//gam:=pB*effEvaluateCBM(b_tilde,Tau)^-1;    //gam is gamma in the article
			"computing gam...";
			gam:=pB*compute_phi_br_tau(array_b_tilde,MF,S,Tau)^-1;
			"done.";
		else print "WRONG permutation";
		end if;
    end if;
until (get_0_1 eq 1) and (InducedPermutation(b_tilde) eq sb);

print "check! VV!vec((gam^-1*nB)^-1,n) in V_article", VV!vec((gam^-1*nB)^-1,n) in V_article;
if not (VV!vec((gam^-1*nB)^-1,n) in V_article) then
	print "Error!!! It may not give all that is needed and had to be another attempt to increase dimension";
end if;

/* -----------  stage 2 ---------- */
/* ======================================== */

min_poly_m0:=MinimalPolynomial(m0);
deg_m_p:= Degree(min_poly_m0);

seq_Mm0:=[];
for i:= 1 to deg_m_p do
	seq_Mm0[i]:=vec(gam^-1*m0^(i-1),n);
end for;

M_c_tilde:= Matrix(seq_Mm0);   //Matrix(seq_Mm0) the rows are seq_Mm0[]. we can use also the command Matrix(R,n,Q) if we need..
M_c_tilde:= ChangeRing( M_c_tilde,F);


basis_phi_P:=final_base_phi;                                       //basis to the algebra generated by the above set of phi(beta_i)
//vec_basis_phi_P:= [vec(basis_phi_P[i],n) : i in [1..#basis_phi_P]];
//vec_basis_phi_P:= v_base_phi;
vec_basis_phi_P:= final_v_base_phi;
conditions:= Basis(NullSpace(Transpose(Matrix(vec_basis_phi_P))));

conditions_matrix:= Transpose(Matrix(conditions));

ker_c:=Nullspace(M_c_tilde*conditions_matrix);
print "Dimension of ker_c:", Dimension(ker_c);

//"vec_nB in ker_c", vec(nB,n) in ker_c;

basis_ker_c:=Basis(ker_c);
v_basis_ker_c:=[];
for i:= 1 to #basis_ker_c do	
	temp:=ZeroMatrix(F,n,n);
	for j:= 1 to deg_m_p do
		temp:=temp+basis_ker_c[i][j]*m0^(j-1);
	end for;
	v_basis_ker_c[i]:=VV!vec(temp,n);
end for;

v_try:=sub<VV|v_basis_ker_c>;
"vec_nB in <basis_ker_c>" , vec(nB,n) in v_try;


VV:=VectorSpace(F, n^2);
//ker_c_seq := SetToSequence(Generators(ker_c));

nB_tilde := random_sp_seq(VV,v_basis_ker_c,F);                 //choosing an invertible element


/* -----------  stage 3  ---------- */
/* ======================================== */


alpha_tag_bob:= nB_tilde^-1*gam;
xxx:=gam^-1*nB_tilde;


R_phi_alpha_matrix:= Matrix(vec_basis_phi_P); //the matrix's row consist from the vectorization of phi(alpha_i)
vec_alpha_tag:=vec(alpha_tag_bob,n);
vec_alpha_tag:=ChangeRing(vec_alpha_tag,F);
li,nullsp:=Solution(R_phi_alpha_matrix,vec_alpha_tag);

if (Dimension(nullsp) eq 0) then print "correct, there is only one solution for li";
else print "problem? there are more than one solution for li";
end if; 

//check
//sum_phi_alphai:= ZeroMatrix(F,n,n);
sum_phi_alphai:=VV!0;
for i:= 1 to #basis_phi_P do
	sum_phi_alphai:=VV!(sum_phi_alphai+li[i]*vec_basis_phi_P[i]);
end for;
if sum_phi_alphai eq VV!vec(alpha_tag_bob,n) then print "correct linear combination for alpha' ";
else print "error!!! wrong linear combination for alpha' ";
end if;
//end check



//sbTau_inversre:=PermAction_on_Tau(sb^-1,Tau);  //this is the "h^-1 "
beta_tag:= ZeroMatrix(F,n,n);
for i:= 1 to #final_base_for_betta1 do
	beta_tag:=beta_tag+li[i]*final_base_for_betta1[i];  //try_base_betta from commands
end for;

phi_b_tilde_sa:=compute_phi_br_tau(array_b_tilde,MF,S, saTau);
recovered_key:= nB_tilde*pA*beta_tag*phi_b_tilde_sa;


if recovered_key eq KA then print "Successful recovery!";
else print "recovey failed";
end if;
