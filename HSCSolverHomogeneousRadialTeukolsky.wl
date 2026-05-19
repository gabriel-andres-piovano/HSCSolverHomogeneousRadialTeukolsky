(* ::Package:: *)

(* ::Section:: *)
(*Begin package*)


BeginPackage["HSCSolverHomogeneousRadialTeukolsky`"];


TsolverInres::usage = "TsolverInres[s,l,m,a,\[Omega],\[Lambda],r1g,intOption] gives the rescaled In solution and its first-order derivative of the homogeneous radial Teukolsky equation. r1g is the outermost integration radius.";


TsolverUpres::usage = "TsolverUpres[s,l,m,a,\[Omega],\[Lambda],r2g,intOption] gives the rescaled Up solution and its first-order derivative of the homogeneous radial Teukolsky equation. r2g is the innermost integration radius.";


TsolverIn::usage = "TsolverIn[s,l,m,a,\[Omega],\[Lambda],r1g,intOption] gives the In solution and its first-order derivative of the homogeneous radial Teukolsky equation. r1g is the outermost integration radius.";


TsolverUp::usage = "TsolverUp[s,l,m,a,\[Omega],\[Lambda],r2g,intOption] gives the Up solution and its first-order derivative of the homogeneous radial Teukolsky equation. r2g is the innermost integration radius.";


TsolverUpNearHorizon::usage = "TsolverUpNearHorizon[s,l,m,a,\[Omega],\[Lambda],{\[Psi]up,d\[Psi]up}] provides the boundary condition near the horizon for the Up solution of the Teukolsky equation."


TsolverIn1spin::usage = "TsolverIn[s,l,m,a,\[Omega]0,\[Omega]1,\[Lambda]0,\[Lambda]1,r1g,intOption] gives the derivative wrt the frequency of the In solution and its first-order derivative of the homogeneous radial Teukolsky equation. r1g is the outermost integration radius.";


TsolverUp1spin::usage = "TsolverUp[s,l,m,a,\[Omega]0,\[Omega]1,\[Lambda]0,\[Lambda]1,r2g,intOption] gives the derivative wrt the frequency of the Up solution and its first-order derivative of the homogeneous radial Teukolsky equation. r2g is the innermost integration radius.";


Begin["`Private`"];


(* ::Section::Closed:: *)
(*Functions for BCs and Teukolsky solver in HS coordinates*)


(* ::Subsection::Closed:: *)
(*Coefficients Teukolsky equation in hyperboloidal slicing*)


TeukolskyHSCoefficients:=Module[{M=1,r,m,a,\[Omega],\[Lambda],\[CapitalDelta],s,f,H,Gtilde,Utilde,p,q,coefficients},
	\[CapitalDelta] = r^2-2M r+a^2;
	f = \[CapitalDelta]/(r^2+a^2); (*dr/drstar*)
	Gtilde = a^2*\[CapitalDelta]+(r^2+a^2)(r*s(r-M)-I*r((r^2+a^2)\[Omega]*H+m*a));
	Utilde = 2I*s*\[Omega]*r^2(r*\[CapitalDelta](1-H)-M(r^2-a^2)(1+H))-2I*a*r*\[CapitalDelta](m+a*\[Omega]*H)+\[CapitalDelta](2a^2-r^2*\[Lambda]-2M*r(s+1))-2m*a*\[Omega]*r^2(r^2+a^2)(1+H)+r^2(r^2+a^2)^2(\[Omega]^2(1-H^2)+I*\[Omega]*f*D[H,r]);
	p = (r^2+a^2)/\[CapitalDelta]*D[f,r]-1/(\[CapitalDelta](r^2+a^2))(2Gtilde)/r;
	q =  Utilde/(r^2*\[CapitalDelta]^2);

	coefficients = {Function@@{p}/.Thread[{r,H,s,m,a,\[Omega],\[Lambda]}->Array[Slot,7]], Function@@{q}/.Thread[{r,H,s,m,a,\[Omega],\[Lambda]}->Array[Slot,7]]};
	Remove[r,H,s,m,a,\[Omega],\[Lambda]];
	coefficients
]


(* ::Subsubsection::Closed:: *)
(*Secondary spin corrections*)


TeukolskyHSCoefficients1spin:=Module[{M=1,r,m ,a,\[Omega]0,\[Omega]1,\[Lambda]0,\[Lambda]1,\[CapitalDelta],s,f,H,Gtilda1,Utilda1,p1,q1,coefficients1},
	\[CapitalDelta] = r^2-2M r+a^2;
	f = \[CapitalDelta]/(r^2+a^2); (*dr/drstar*)
	Gtilda1 = -I*H*r (r^2+a^2)^2*\[Omega]1;
	Utilda1 = r(-r*\[CapitalDelta]*\[Lambda]1-2a(1+H)m*r(r^2+a^2)\[Omega]1-2I*a^2*H*\[CapitalDelta]*\[Omega]1+2I*r*s((1+H)M(a-r)(a+r)-(-1+H)r*\[CapitalDelta])\[Omega]1-2(-1+H^2)r (r^2+a^2)^2*\[Omega]0*\[Omega]1);
	 	 
	p1 = -(1/(\[CapitalDelta](r^2+a^2)))(1/r)2Gtilda1;
	q1 = Utilda1/(r^2*\[CapitalDelta]^2);
	 
	coefficients1 = {Function@@{p1}/.Thread[{r,H,s,m,a,\[Omega]0,\[Omega]1,\[Lambda]0,\[Lambda]1}->Array[Slot,9]], Function@@{q1}/.Thread[{r,H,s,m,a,\[Omega]0,\[Omega]1,\[Lambda]0,\[Lambda]1}->Array[Slot,9]]};
	
	Remove[r,H,s,m,a,\[Omega]0,\[Omega]1,\[Lambda]0,\[Lambda]1];
	coefficients1
]


(* ::Subsection::Closed:: *)
(*Boundary condition at the horizon - minus solution*)


bchormin[workingprecision_,s_,m_,a_,\[Omega]_,\[Lambda]_]:=Module[{M=1,deltarp,A2n,rp,rm,rin,err,errold,i,chor,p,q,phor,qhor,dphor,dqhor,\[Psi]hor,a2n,cInHor},
	rp=M+Sqrt[M^2-a^2];
	rm=M-Sqrt[M^2-a^2];
	deltarp=(rp-rm)/50;
	rin=rp+deltarp; (*Closest r to the horizon *)
	chor=2I (2M*rp)/(rp-rm)(\[Omega]-(a*m)/(2M*rp))+s;

	dqhor[n_]:=Which[
					n==0,
					0,
					n==1,
					(2I*a*m+2M(-1+s)-2I*a^2*\[Omega]+rp(2+\[Lambda]-4I*rp*s*\[Omega]))/((rm-rp)rp),
					n>1,
					2(-1+n)(-rp)^(-n)+(rm-rp)^(-n)(2+\[Lambda]-4I*rm*s*\[Omega])+1/rp 2n (rm-rp)^(-n)(M(-1+s)+I*a(m-a*\[Omega]))(1+(1/n)*Sum[Binomial[n,k](-rm)^(k-1)/rp^(k-1),{k,2,n}])
				];

	dphor[n_]:=Which[
					n==0,
					1-chor,
					n==1,
					1/((rm-rp)^2rp)(-2rm^2+a^2(3+2s+4I*rp*\[Omega])+I*rp(-2a*m+2a^2*\[Omega]+I(rp+2M*s+2I*rp^2*\[Omega]))),
					n>1,
					2(-rp)^(-n)-(rm-rp)^(-n)+(rm-rp)^(-n-1) (rm(+2s)+2I*rm^2*\[Omega]+2I(-a*m+I*M*s+a^2*\[Omega]))
				];

	a2n[0]=1;
	A2n[n_]:= -(1/(n(n-chor)))Sum[(j*dphor[n-j]+dqhor[n-j])a2n[j],{j,0,n-1}];

	err=1;
	errold=1;
	i=1;
	{p,q}=TeukolskyHSCoefficients;
	phor=p[rin,-1,s,m,a,\[Omega],\[Lambda]];
	qhor=q[rin,-1,s,m,a,\[Omega],\[Lambda]];

	While[err > 10^(-workingprecision),
		If[Mod[i,30]==0,
			deltarp=deltarp/2;
			rin=N[rp+deltarp,workingprecision];
			phor=p[rin,-1,s,m,a,\[Omega],\[Lambda]];
			qhor=q[rin,-1,s,m,a,\[Omega],\[Lambda]];
		];
        a2n[i]=A2n[i];
		\[Psi]hor=Evaluate[1+Sum[a2n[k](#-rp)^k,{k,i}]]&;
		err=Abs[\[Psi]hor''[rin]+phor*\[Psi]hor'[rin]+qhor*\[Psi]hor[rin]];

		If[errold<=err&&errold> 10^(-workingprecision)&&i>5,
			Break[];
			,
			errold=err;
		];
		i++;

		If[i > 100, Break[]] (*Safeguard to avoid ruwaway computation*)   
	];
	cInHor=Table[a2n[k],{k,0,i-1}]; (*Coefficients for ingoing waves near horizon (-)*)
	{cInHor,rin}
]


(* ::Subsection::Closed:: *)
(*Boundary condition at infinity - plus solution*)


bcinfplus[workingprecision_,s_,m_,a_,\[Omega]_,\[Lambda]_]:=Module[{M=1,B1n,rp,rm,rout,err,i,p,q,pinf,qinf,dpinf,dqinf,\[Psi]inf,b1n,cOutinf},
	rp=M+Sqrt[M^2-a^2];
	rm=M-Sqrt[M^2-a^2];
	rout=2\[Pi](1/Abs[\[Omega]]+Abs[\[Omega]]/(1+Abs[\[Omega]]));

	dqinf[n_]:=Which[
					n==0,
					0,
					n==1,
					0,
					n==2,
					-(4a*m*\[Omega]+4I*M*s*\[Omega]+\[Lambda]),n>2,1/(rm-rp)^3 ((rm-rp)^2(2rm^(-2+n) rp-2rm*rp^(-2+n)+2I*a*m(-rm^(-2+n)+rp^(-2+n))+2M(-rm^(-2+n)+rp^(-2+n))(1+s)+(-rm^(-1+n)+rp^(-1+n))\[Lambda])+2I (rm-rp)^2(-rm^(-1+n)*rp+rm*rp^(-1+n))\[Omega]+4(a*m(-rp^n(2M+n*rm-n*rp)+rm^n (2M-n*rm+n*rp)+a^2(rp^(-2+n) (rm-n*rm+(-3+n)rp)+rm^(-2+n) (-(-3+n)rm+(-1+n)rp)))+I*M(-rp^n(2M+n*rm-n*rp)+rm^n (2M-n*rm+n*rp)+a^2(rp^(-2+n) ((-1+n)rm-(-3+n)rp)+rm^(-2+n) ((-3+n)rm+rp-n*rp)))s)\[Omega])
				];

	dpinf[n_]:=Which[
					n==0,
					2I*\[Omega],
					n==1,
					-2s+2I*2M*\[Omega],
					n>1,
					rm^(-1+n)+rp^(-1+n)-(2rp^(-1+n) ((M-rp)s+I(a*m+(a^2+rp^2)\[Omega])))/(rm-rp)+(2rm^(-1+n) ((M-rm)s+I(a*m+(a^2+rm^2)\[Omega])))/(rm-rp)
				];
				
	err=1;
	i=1;
	b1n[0]=1;
	B1n[n_]:=(n-1)/(2I*\[Omega])b1n[n-1]+1/(2I*\[Omega]*n) Sum[(dqinf[j+1]-(n-j)dpinf[j])b1n[n-j],{j,1,n}];

	{p,q}=TeukolskyHSCoefficients;
	pinf=p[rout,1,s,m,a,\[Omega],\[Lambda]];
	qinf=q[rout,1,s,m,a,\[Omega],\[Lambda]];

	While[err > 10^(-workingprecision),
		If[Mod[i,15]==0,
			rout=2rout;
			pinf=p[rout,1,s,m,a,\[Omega],\[Lambda]];
			qinf=q[rout,1,s,m,a,\[Omega],\[Lambda]];
		];
		b1n[i]=B1n[i];
		\[Psi]inf=Evaluate[1+Sum[b1n[k](#)^(-k),{k,i}]]&;
		err=Abs[\[Psi]inf''[rout]+pinf*\[Psi]inf'[rout]+qinf*\[Psi]inf[rout]];
		i++;
		If[i > 150, Break[]] (*Asymptotic expansions are not convergent*)    
	];
	cOutinf=Table[b1n[k],{k,0,i-1}]; (*Coefficients for outgoing waves at \[Infinity] (+)*)
	{cOutinf,rout}
]


(* ::Subsection::Closed:: *)
(*Boundary condition at the horizon - plus solution*)


bchorplus[workingprecision_,s_,m_,a_,\[Omega]_,\[Lambda]_]:=Module[{M=1,\[Kappa],\[CapitalOmega]H,indterm,deltarp,A2n,rp,rm,rin,err,errold,i,phor,qhor,phorfun,qhorfun,dphor,dqhor,\[Psi]hor,a2n,cInHor},
	rp=M+Sqrt[M^2-a^2];
	rm=M-Sqrt[M^2-a^2];
	\[Kappa]=\[Omega]-m*\[CapitalOmega]H;
	\[CapitalOmega]H=a/(2M*rp);
	deltarp=(rp-rm)/50;
	rin=rp+deltarp; (*Closest r to the horizon *)
	indterm=s+2I*M(1+M/Sqrt[-a^2+M^2])\[Kappa];

	dqhor[n_]:=Which[
					n==0,
					0,
					n==1,
					I*\[Kappa](1+s+2I*M*\[Kappa])+I*s*\[Omega]+2M*\[Omega]^2-1/(rp-rm)^3 2(-4a^3*m*\[Omega]+2M^2(\[Lambda]+4M^2(\[Kappa]-\[Omega])(\[Kappa]+\[Omega])-2I*M(\[Kappa]+s*\[Kappa]+s*\[Omega]))+a^2(m^2-2\[Lambda]+4I*M(\[Kappa]+s*\[Kappa]+s*\[Omega])+12M^2(-\[Kappa]^2+\[Omega]^2))),
					n==2,
					-((I(a*m(s+2I*M*\[Omega])+4*a^2(\[Kappa](1+s+2I*M*\[Kappa])+s*\[Omega]-2I*M*\[Omega]^2)+2M^2(-\[Kappa](2+s+2I*M*\[Kappa])-3s*\[Omega]+2I*M*\[Omega]^2)))/(rp-rm)^3)+1/(rp-rm)^4(-8a^3*m*\[Omega]-4a*m*M^2*\[Omega]+16a^4(-\[Kappa]^2+\[Omega]^2)+a^2(3m^2-4\[Lambda]+12*M^2(\[Kappa]-\[Omega])(\[Kappa]+\[Omega])+4I*M((2+s)\[Kappa]+3s*\[Omega]))+4M^2(\[Lambda]-I*M((2+s)\[Kappa]+3s*\[Omega])+2M^2(-\[Kappa]^2+\[Omega]^2))),
					n>2,
					-1/(rp-rm)I*2^(-n)(-Sqrt[-a^2+M^2])^(-n)(a*m(-1+n)(s+2I*M*\[Omega])+4a^2(\[Kappa](1+s+2I*M*\[Kappa])+s*\[Omega]-2I*M*\[Omega]^2)+2M^2 (\[Kappa](-2+(-3+n) s+2 I M (-3+n) \[Kappa])-(1+n) s*\[Omega]-2I*M(-3+n)\[Omega]^2))-1/(rp-rm)^2 2^(-n)(-Sqrt[-a^2+M^2])^(-n)(8a^3*m*\[Omega]+4a*m*M^2(-1+n)\[Omega]+4M^2(-\[Lambda]+2M^2(-3+n)(\[Kappa]-\[Omega])(\[Kappa]+\[Omega])-I*M((-2+(-3+n)s)\[Kappa]-(1+n)s*\[Omega]))+a^2(-m^2(1+n)+4\[Lambda]-4*M^2(-7+n)(\[Kappa]-\[Omega])(\[Kappa]+\[Omega])+4I*M((-2+(-3+n)*s)\[Kappa]-(1+n)s*\[Omega])))
				];

	dphor[n_]:=Which[
					n==0,
					(2(M-rp)(1+s)-2I(a^2+rp^2)\[Kappa])/(rm-rp),
					n==1,
					(2(M-rm)(1+s)-2I(a^2+(2rm-rp)rp)\[Kappa])/(rm-rp)^2,
					n>1,(rm-rp)^(-1-n)(2(M-rm)(1+s)-2I(a^2+rm^2)\[Kappa])
				];

	a2n[0]=1;
	A2n[n_]:= -(1/(n(n+indterm)))Sum[(j*dphor[n-j]+dqhor[n-j])a2n[j],{j,0,n-1}];

	err=1;
	errold=1;
	i=1;
	phorfun[r_]:=(-2(M-r)(1+s)+2I(a^2+r^2)\[Kappa])/((r-rp)(r-rm));
	qhorfun[r_]:=qhor=(2I(a^2(r-M*s+r*s)+r^2 (r(1+s)-M(2+s)))\[Kappa])/((r-rp)^2(r-rm)^2)-((a^2+r^2)^2*\[Kappa]^2)/((r-rp)^2(r-rm)^2)+1/((r-rp)^2(r-rm)^2)(-2a^3*m*\[Omega]+a^4*\[Omega]^2-2I*a*m(M*s+r(-s-I*r*\[Omega]))+a^2(m^2-\[Lambda]+2\[Omega](I*M*s+I*r*s+r^2*\[Omega]))+r(2M(\[Lambda]-3I*r*s*\[Omega])+r(-\[Lambda]+r*\[Omega](2I*s+r*\[Omega]))));

	phor=phorfun[rin];
	qhor=qhorfun[rin];

	While[err > 10^(-workingprecision),
		If[Mod[i,30]==0,
			deltarp=deltarp/2;
			rin=N[rp+deltarp,workingprecision];
			phor=phorfun[rin];
			qhor=qhorfun[rin];
		];
        a2n[i]=A2n[i];
		\[Psi]hor=Evaluate[1+Sum[a2n[k](#-rp)^k,{k,i}]]&;
		err=Abs[\[Psi]hor''[rin]+phor*\[Psi]hor'[rin]+qhor*\[Psi]hor[rin]];

		If[errold<=err&&errold> 10^(-workingprecision)&&i>5,
			Break[];
			,
			errold=err;
		];
		i++;

		If[i > 100, Break[]] (*Safeguard to avoid ruwaway computation*)   
	];
	cInHor=Table[a2n[k],{k,0,i-1}]; (*Coefficients for outgoing wave near horizon (+)*)
	{cInHor,rin}
]


(* ::Subsection::Closed:: *)
(*Boundary condition at infinity - minus solution*)


bcinfmin[workingprecision_,s_,m_,a_,\[Omega]_,\[Lambda]_]:=Module[{M=1,B1n,rp,rm,rout,err,i,pfun,qfun,pinf,qinf,dpinf,dqinf,\[Psi]inf,b1n,cOutinf,\[Xi]},
	rp=M+Sqrt[M^2-a^2];
	rm=M-Sqrt[M^2-a^2];
	rout=2\[Pi](1/Abs[\[Omega]]+Abs[\[Omega]]/(1+Abs[\[Omega]]));

	dqinf[n_]:=Which[
					n==0,
					0,
					n==1,
					0,
					n==2,
					-\[Lambda]-2a*m*\[Omega]+s(-2-4I*M*\[Omega]),
					n>2,
					(2 rm^(-2+n))/(rm-rp)^3 (-2 M (-3+n) rp^2+2 (-4+n) a^2rp+M (-1+n) rm^2 \[Lambda]+2 M^2 (2 rp (-2+n+s)-n rm \[Lambda])-4 I a^4 \[Omega]-16 I M^4 (-1+n) s \[Omega]+2 a^3 m (-I (-1+n) s+2 (M+M n-rp) \[Omega])+2 a m M^2 (-1+n) (I s+2 (-2 M+rp) \[Omega])+4 M^3 (-1-s+2 I (-1+n) rp s \[Omega])+a^2 ((2+m^2) (-2+n) rm-4 rp s+2 rm \[Lambda]+4 I M^2 (1+4 (-1+n) s) \[Omega]+M (18+m^2-6 n-m^2 n+4 s-\[Lambda]+n \[Lambda]-8 I (-1+n) rp s \[Omega])))+(2 rp^(-2+n))/(-rm+rp)^3 (-2 M (-3+n) rm^2+2 (-4+n) a^2rm+M (-1+n) rp^2 \[Lambda]+2 M^2 (2 rm (-2+n+s)-n rp \[Lambda])-4 I a^4 \[Omega]-16 I M^4 (-1+n) s \[Omega]+2 a^3 m (-I (-1+n) s+2 (M+M n-rm) \[Omega])+2 a m M^2 (-1+n) (I s+2 (-2 M+rm) \[Omega])+4 M^3 (-1-s+2 I (-1+n) rm s \[Omega])+a^2 ((2+m^2) (-2+n) rp-4 rm s+2 rp \[Lambda]+4 I M^2 (1+4 (-1+n) s) \[Omega]+M (18+m^2-6 n-m^2 n+4 s-\[Lambda]+n \[Lambda]-8 I (-1+n) rm s \[Omega])))
				];

	dpinf[n_]:=Which[
					n==0,
					-2I*\[Omega],
					n==1,
					2s-2I*2M*\[Omega],
					n>1,
					(2 rm^(-1+n) (M-rp-M*s+rm*s-I*rm^2*\[Omega]-I*rm*rp*\[Omega]))/(rm-rp)+(2 rp^(-1+n) (-M+rm+M*s-rp*s+I*rm*rp*\[Omega]+I*rp^2*\[Omega]))/(rm-rp)
				];

	err=1;
	i=1;
	b1n[0]=1;
	\[Xi]=0;
	B1n[n_]:=-(((n-\[Xi])(n-1-\[Xi]))/(2I*\[Omega]*n))b1n[n-1]-1/(2I*\[Omega]*n) Sum[(dqinf[j+1]-(n-j-\[Xi])dpinf[j])b1n[n-j],{j,1,n}];

	pfun[r_]:=r/((r-rp)(r-rm)) ((2 (-a^2+M*r-M*r*s+r^2*s))/r^2-(2I(a^2+r^2)\[Omega])/r);

	qfun[r_]:=1/(r^2(r-rm)^2(r-rp)^2) (-2 a^3 m r^2 \[Omega]+a^4 (2+2 I r \[Omega])-2 a m r^2 (I M s+r (-I s+r \[Omega]))+r^2 (-4 M^2 (-1+s)-r^2 (2 s+\[Lambda])+2 M r (-1+3 s+\[Lambda]-2 I r s \[Omega]))+a^2 r (r (2+m^2-2 s-\[Lambda]+2 I r \[Omega])+2 M (-3+s-2 I r \[Omega]+2 I r s \[Omega])));

	pinf=pfun[rout];
	qinf=qfun[rout];

	While[err > 10^(-workingprecision),
			If[Mod[i,15]==0,
				rout=2rout;
				pinf=pfun[rout];
				qinf=qfun[rout];
			];
			b1n[i]=B1n[i];
			\[Psi]inf=Evaluate[(1+Sum[b1n[k](#)^(-k),{k,i}])]&;
			err=Abs[\[Psi]inf''[rout]+pinf \[Psi]inf'[rout]+qinf \[Psi]inf[rout]];
			i++;
			If[i > 150, Break[]]  (*Asymptotic expansions are not convergent*)    
	];
	cOutinf=Table[b1n[k],{k,0,i-1}]; (*Coefficients for outgoing waves at \[Infinity] (+)*)
	{cOutinf,rout}
]


(* ::Subsection::Closed:: *)
(*Teukolsky solver in hyperboloidal slicing coordinates *)


(* ::Subsubsection::Closed:: *)
(*In solution rescaled*)


TsolverInres[s_,l_,m_,a_,\[Omega]_,\[Lambda]_,r1g_,intorder_]:=Module[{workODE,precBC,precGoal,accGoal,rin,rp,rm,p,q,cInH,\[Psi]hor,eqhor,r,rtor,X,Y,\[Psi]in,d\[Psi]in,nmaxhor},
	rp=1+Sqrt[1-a^2];
	rm=1-Sqrt[1-a^2];
	If[(Precision[a]==MachinePrecision)||(Precision[\[Omega]]==MachinePrecision)||(Precision[\[Lambda]]==MachinePrecision)||(Precision[r1g]==MachinePrecision),
		workODE=MachinePrecision;
		precGoal=13;
		accGoal=13;
		precBC=15;
		,
		workODE=Min[{Precision[a]-5,Precision[\[Omega]]-5,Precision[\[Lambda]]-5,Precision[r1g]-5}];
		precGoal=workODE-5;
		accGoal=workODE-5;
		precBC=Min[{Precision[a],Precision[\[Omega]],Precision[\[Lambda]],Precision[r1g]}];
	];

	{p,q}=TeukolskyHSCoefficients;

	{cInH,rin}=bchormin[precBC,s,m,a,\[Omega],\[Lambda]];
	nmaxhor=Length[cInH];
	\[Psi]hor=Evaluate[Sum[cInH[[i]](#-rp)^(i-1),{i,nmaxhor}]]&;

	eqhor={
			X'[r]== Y[r],
			Y'[r]==-p[r,-1,s,m,a,\[Omega],\[Lambda]]Y[r]-q[r,-1,s,m,a,\[Omega],\[Lambda]] X[r],
			X[rin]==\[Psi]hor[rin],Y[rin]== \[Psi]hor'[rin]
		};

	{\[Psi]in,d\[Psi]in}={X,Y}/.First@NDSolve[eqhor,{X,Y},{r,rin,r1g},Method->"StiffnessSwitching",WorkingPrecision->workODE,PrecisionGoal->precGoal,AccuracyGoal->accGoal,InterpolationOrder->intorder];

	(* Remove local variables not garbage collected*)
	ClearSystemCache[];
	Remove[Evaluate[ToExpression[Pick[Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],StringMatchQ[#,"HSCSolverHomogeneousRadialTeukolsky`Private`X$"~~__]&/@Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],True]]]];
	Remove[Evaluate[ToExpression[Pick[Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],StringMatchQ[#,"HSCSolverHomogeneousRadialTeukolsky`Private`Y$"~~__]&/@Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],True]]]];
	Remove[r];

	{Function[{r},Evaluate[If[r<=rin,Evaluate[\[Psi]hor[r]],Evaluate[\[Psi]in[r]]]],Listable],Function[{r},Evaluate[If[r<=rin,Evaluate[\[Psi]hor'[r]],Evaluate[d\[Psi]in[r]]]],Listable],rin}
]


(* ::Subsubsection::Closed:: *)
(*Up solution rescaled*)


TsolverUpres[s_,l_,m_,a_,\[Omega]_,\[Lambda]_,r2g_,intorder_]:=Module[{workODE,precBC,precGoal,accGoal,rout,p,q,cOutinf,\[Psi]inf,eqinf,r,X,Y,\[Psi]up,d\[Psi]up,nmaxinf},
	If[(Precision[a]==MachinePrecision)||(Precision[\[Omega]]==MachinePrecision)||(Precision[\[Lambda]]==MachinePrecision)||(Precision[r2g]==MachinePrecision),
		workODE=MachinePrecision;
		precGoal=13;
		accGoal=13;
		precBC=15;
		,
		workODE=Min[{Precision[a]-5,Precision[\[Omega]]-5,Precision[\[Lambda]]-5,Precision[r2g]-5}];
		precGoal=workODE-5;
		accGoal=workODE-5;
		precBC=Min[{Precision[a],Precision[\[Omega]],Precision[\[Lambda]],Precision[r2g]}];
	];

	{p,q}=TeukolskyHSCoefficients;

	{cOutinf,rout}=bcinfplus[precBC,s,m,a,\[Omega],\[Lambda]];
	nmaxinf=Length[cOutinf];
	\[Psi]inf=Evaluate[Sum[cOutinf[[i]]#^(-i+1),{i,nmaxinf}]]&;

	eqinf={
			X'[r]== Y[r],
			Y'[r]==-p[r,1,s,m,a,\[Omega],\[Lambda]]Y[r]-q[r,1,s,m,a,\[Omega],\[Lambda]] X[r],
			X[rout]==\[Psi]inf[rout],Y[rout]==\[Psi]inf'[rout]
		};  

	{\[Psi]up,d\[Psi]up}={X,Y}/.First@NDSolve[eqinf,{X,Y},{r,r2g,rout},Method->"StiffnessSwitching",WorkingPrecision->workODE,PrecisionGoal->precGoal,AccuracyGoal->accGoal,InterpolationOrder->intorder];

	(* Remove local variables not garbage collected*)
	ClearSystemCache[];
	Remove[Evaluate[ToExpression[Pick[Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],StringMatchQ[#,"HSCSolverHomogeneousRadialTeukolsky`Private`X$"~~__]&/@Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],True]]]];
	Remove[Evaluate[ToExpression[Pick[Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],StringMatchQ[#,"HSCSolverHomogeneousRadialTeukolsky`Private`Y$"~~__]&/@Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],True]]]];
	Remove[r];

	{Function[{r},Evaluate[If[r>=rout,Evaluate[\[Psi]inf[r]],Evaluate[\[Psi]up[r]]]],Listable],Function[{r},Evaluate[If[r>=rout,Evaluate[\[Psi]inf'[r]],Evaluate[d\[Psi]up[r]]]],Listable],rout}
]


(* ::Subsubsection::Closed:: *)
(*In solution*)


TsolverIn[s_,l_,m_,a_,\[Omega]_,\[Lambda]_,r1g_,intorder_]:=Module[{workODE,precBC,precGoal,accGoal,rin,rout,routplus,routmin,rp,rm,resfac,dfacexp,p,q,cInH,\[Psi]hor,cOutinfplus,cOutinfmin,nmaxinfplus,nmaxinfmin,eqhor,r,rtor,\[Alpha],X,Y,\[Psi]in,d\[Psi]in,nmaxhor,\[Psi]infplus,\[Psi]infmin,Bref,Binc,Rinfplus,dRinfplus,Rinfmin,dRinfmin,Rin,dRin,B1,B2},
	rp=1+Sqrt[1-a^2];
	rm=1-Sqrt[1-a^2];
	rtor=Evaluate[(2rp)/(rp-rm) Log[(#-rp)/2]-(2rm)/(rp-rm) Log[(#-rm)/2]+#]&;
	\[Alpha]=rp Exp[I*a*m(1/2+1/rp Log[(rp-rm)/2])];
	resfac=Evaluate[Function[{H,r},1/r(r^2-2r+a^2)^(-s)Exp[H*I*\[Omega]*rtor[r]]Exp[I*m*a/(rp-rm)(Log[(r-rp)/(r-rm)])]]];
	dfacexp=Function[{H,r},-(1/r +(2s(r-1))/(r^2-2r+a^2))+I/(r^2-2r+a^2) (H(r^2+a^2)\[Omega]+a m)];

	If[(Precision[a]==MachinePrecision)||(Precision[\[Omega]]==MachinePrecision)||(Precision[\[Lambda]]==MachinePrecision)||(Precision[r1g]==MachinePrecision),
		workODE=MachinePrecision;
		precGoal=13;
		accGoal=13;
		precBC=15;
		,
		workODE=Min[{Precision[a]-5,Precision[\[Omega]]-5,Precision[\[Lambda]]-5,Precision[r1g]-5}];
		precGoal=workODE-5;
		accGoal=workODE-5;
		precBC=Min[{Precision[a],Precision[\[Omega]],Precision[\[Lambda]],Precision[r1g]}];
	];

	{p,q}=TeukolskyHSCoefficients;

	{cInH,rin}=bchormin[precBC,s,m,a,\[Omega],\[Lambda]];
	nmaxhor=Length[cInH];
	\[Psi]hor=Evaluate[Sum[cInH[[i]](#-rp)^(i-1),{i,nmaxhor}]]&;

	{cOutinfplus,routplus}=bcinfplus[precBC,s,m,a,\[Omega],\[Lambda]];
	{cOutinfmin,routmin}=bcinfmin[precBC,s,m,a,\[Omega],\[Lambda]];
	nmaxinfplus=Length[cOutinfplus];
	nmaxinfmin=Length[cOutinfmin];
	rout=Max[{routplus,routmin}];

	\[Psi]infplus=Evaluate[Sum[cOutinfplus[[i]]#^(-i+1),{i,nmaxinfplus}]]&;
	\[Psi]infmin=Evaluate[Sum[cOutinfmin[[i]]#^(-i+1),{i,nmaxinfmin}]]&;

	Rinfplus=Evaluate[resfac[1,#]\[Psi]infplus[#]]&;
	dRinfplus=Evaluate[Rinfplus[#] dfacexp[1,#]+resfac[1,#]\[Psi]infplus'[#]]&;
	Rinfmin=Evaluate[(1/#)*Exp[-I*\[Omega]*rtor[#]]\[Psi]infmin[#]]&;
	dRinfmin=Evaluate[Rinfmin[#](-(1/#)-(I*\[Omega](a^2+#^2))/((#-rm)(#-rp)))+(1/#)Exp[-I*\[Omega]*rtor[#]]\[Psi]infmin'[#]]&;

	eqhor={
			X'[r]== Y[r],
			Y'[r]==-p[r,-1,s,m,a,\[Omega],\[Lambda]]Y[r]-q[r,-1,s,m,a,\[Omega],\[Lambda]] X[r],
			X[rin]==\[Psi]hor[rin],Y[rin]== \[Psi]hor'[rin]
		};

	If[r1g>=rout,
		{\[Psi]in,d\[Psi]in}={X,Y}/.First@NDSolve[eqhor,{X,Y},{r,rin,rout},Method->"StiffnessSwitching",WorkingPrecision->workODE,PrecisionGoal->precGoal,AccuracyGoal->accGoal,InterpolationOrder->intorder];

		{Bref,Binc}={B1,B2}/.NSolve[B1*Rinfplus[rout]+B2*Rinfmin[rout]==(\[Alpha]*resfac[-1,rout]\[Psi]in[rout])&&B1*dRinfplus[rout]+B2*dRinfmin[rout]==(\[Alpha]*resfac[-1,rout](dfacexp[-1,rout]\[Psi]in[rout]+d\[Psi]in[rout])),{B1,B2}][[1]];

		Rin=Function[{r},Evaluate[If[r<=rout,
									Evaluate[If[r>=rin,Evaluate[\[Alpha]*resfac[-1,r]\[Psi]in[r]],Evaluate[\[Alpha]*resfac[-1,r]\[Psi]hor[r]]]]
									,
									Evaluate[{Bref,Binc} . {Rinfplus[r],Rinfmin[r]}]
									]],Listable];
		dRin=Function[{r},Evaluate[If[r<=rout,
										Evaluate[If[r>=rin,Evaluate[\[Alpha]*resfac[-1,r](dfacexp[-1,r]\[Psi]in[r]+d\[Psi]in[r])],Evaluate[\[Alpha]*resfac[-1,r](dfacexp[-1,r]\[Psi]hor[r]+\[Psi]hor'[r])]]]
										,
										Evaluate[{Bref,Binc} . {dRinfplus[r],dRinfmin[r]}]
									]],Listable];
		,
		{\[Psi]in,d\[Psi]in}={X,Y}/.First@NDSolve[eqhor,{X,Y},{r,rin,r1g},Method->"StiffnessSwitching",WorkingPrecision->workODE,PrecisionGoal->precGoal,AccuracyGoal->accGoal,InterpolationOrder->intorder];

		Rin=Function[{r},Evaluate[If[r<=rin,Evaluate[\[Alpha]*resfac[-1,r]\[Psi]hor[r]],Evaluate[\[Alpha] resfac[-1,r]\[Psi]in[r]]]],Listable];
		dRin=Function[{r},Evaluate[If[r<=rin,Evaluate[\[Alpha]*resfac[-1,r](dfacexp[-1,r]\[Psi]hor[r]+\[Psi]hor'[r])],Evaluate[\[Alpha]*resfac[-1,r](dfacexp[-1,r]\[Psi]in[r]+d\[Psi]in[r])]]],Listable];
	];
	(* Remove local variables not garbage collected*)
	ClearSystemCache[];
	Remove[Evaluate[ToExpression[Pick[Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],StringMatchQ[#,"HSCSolverHomogeneousRadialTeukolsky`Private`X$"~~__]&/@Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],True]]]];
	Remove[Evaluate[ToExpression[Pick[Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],StringMatchQ[#,"HSCSolverHomogeneousRadialTeukolsky`Private`Y$"~~__]&/@Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],True]]]];
	Remove[r];

	{Rin,dRin,{rin,rout}}
]


(* ::Subsubsection::Closed:: *)
(*Up solution*)


TsolverUp[s_,l_,m_,a_,\[Omega]_,\[Lambda]_,r2g_,intorder_]:=Module[{workODE,precBC,precGoal,accGoal,rin,rout,rinplus,rinmin,rp,rm,\[Kappa],\[CapitalOmega]H,resfac,dfacexp,p,q,\[Psi]inf,cOutinf,nmaxinf,eqinf,r,rtor,\[Alpha],X,Y,\[Psi]up,d\[Psi]up,cInHplus,cInHmin,nmaxhorplus,nmaxhormin,\[Psi]horplus,\[Psi]hormin,Cref,Cinc,Rhorplus,dRhorplus,Rhormin,dRhormin,Rup,dRup,C1,C2},
	rp=1+Sqrt[1-a^2];
	rm=1-Sqrt[1-a^2];
	\[Kappa]=\[Omega]-m*\[CapitalOmega]H;
	\[CapitalOmega]H=a/(2rp);
	rtor=Evaluate[(2rp)/(rp-rm) Log[(#-rp)/2]-(2rm)/(rp-rm) Log[(#-rm)/2]+#]&;
	\[Alpha]=rp*Exp[I*a*m(1/2+1/rp Log[(rp-rm)/2])];
	resfac=Evaluate[Function[{H,r},1/r(r^2-2r+a^2)^(-s)Exp[H*I*\[Omega]*rtor[r]]Exp[I*m*a/(rp-rm)(Log[(r-rp)/(r-rm)])]]];
	dfacexp=Function[{H,r},-(1/r +(2s(r-1))/(r^2-2r+a^2))+I/(r^2-2r+a^2) (H(r^2+a^2)\[Omega]+a m)];

	If[(Precision[a]==MachinePrecision)||(Precision[\[Omega]]==MachinePrecision)||(Precision[\[Lambda]]==MachinePrecision)||(Precision[r2g]==MachinePrecision),
		workODE=MachinePrecision;
		precGoal=13;
		accGoal=13;
		precBC=15;
		,
		workODE=Min[{Precision[a]-5,Precision[\[Omega]]-5,Precision[\[Lambda]]-5,Precision[r2g]-5}];
		precGoal=workODE-5;
		accGoal=workODE-5;
		precBC=Min[{Precision[a],Precision[\[Omega]],Precision[\[Lambda]],Precision[r2g]}];
	];

	{p,q}=TeukolskyHSCoefficients;

	{cOutinf,rout}=bcinfplus[precBC,s,m,a,\[Omega],\[Lambda]];
	nmaxinf=Length[cOutinf];
	\[Psi]inf=Evaluate[Sum[cOutinf[[i]]#^(-i+1),{i,nmaxinf}]]&;

	{cInHplus,rinplus}=bchorplus[precBC,s,m,a,\[Omega],\[Lambda]];
	{cInHmin,rinmin}=bchormin[precBC,s,m,a,\[Omega],\[Lambda]];
	nmaxhorplus=Length[cInHplus];
	nmaxhormin=Length[cInHmin];
	rin=Max[{rinplus,rinmin}];

	\[Psi]horplus=Evaluate[Sum[cInHplus[[i]](#-rp)^(i-1),{i,nmaxhorplus}]]&;
	\[Psi]hormin=Evaluate[Sum[cInHmin[[i]](#-rp)^(i-1),{i,nmaxhormin}]]&;

	Rhorplus=Evaluate[Exp[I*\[Kappa]*rtor[#]]\[Psi]horplus[#]]&;
	dRhorplus=Evaluate[Rhorplus[#] (I*\[Kappa](a^2+#^2))/((#-rm)(#-rp))+Exp[I \[Kappa] rtor[#]]\[Psi]horplus'[#]]&;
	Rhormin=Evaluate[\[Alpha]*resfac[-1,#]\[Psi]hormin[#]]&;
	dRhormin=Evaluate[Rhormin[#] dfacexp[-1,#]+\[Alpha]*resfac[-1,#]\[Psi]hormin'[#]]&;

	eqinf={
			X'[r]== Y[r],
			Y'[r]==-p[r,1,s,m,a,\[Omega],\[Lambda]]Y[r]-q[r,1,s,m,a,\[Omega],\[Lambda]] X[r],
			X[rout]==\[Psi]inf[rout],Y[rout]== \[Psi]inf'[rout]
		};

	If[r2g>=rout,
		Rup=Function[{r},Evaluate[resfac[1,r]\[Psi]inf[r]],Listable];
		dRup=Function[{r},Evaluate[resfac[1,r](dfacexp[1,r]\[Psi]inf[r]+\[Psi]inf'[r])],Listable];
		,
		If[r2g<=rin,
			{\[Psi]up,d\[Psi]up}={X,Y}/.First@NDSolve[eqinf,{X,Y},{r,rin,rout},Method->"StiffnessSwitching",WorkingPrecision->workODE,PrecisionGoal->precGoal,AccuracyGoal->accGoal,InterpolationOrder->intorder];

			{Cinc,Cref}={C1,C2}/.NSolve[C1*Rhorplus[rin]+C2*Rhormin[rin]==(resfac[1,rin]\[Psi]up[rin])&&C1*dRhorplus[rin]+C2 dRhormin[rin]==(resfac[1,rin](dfacexp[1,rin]\[Psi]up[rin]+d\[Psi]up[rin])),{C1,C2}][[1]];

			Rup=Function[{r},Evaluate[If[r>=rin,
								Evaluate[If[r<=rout,Evaluate[resfac[1,r]\[Psi]up[r]],Evaluate[resfac[1,r]\[Psi]inf[r]]]]
								,
								Evaluate[{Cinc,Cref} . {Rhorplus[r],Rhormin[r]}]
							]],Listable];
			dRup=Function[{r},Evaluate[If[r>=rin,
								Evaluate[If[r<=rout,Evaluate[resfac[1,r](dfacexp[1,r]\[Psi]up[r]+d\[Psi]up[r])],Evaluate[resfac[1,r](dfacexp[1,r]\[Psi]inf[r]+\[Psi]inf'[r])]]]
								,
								Evaluate[{Cinc,Cref} . {dRhorplus[r],dRhormin[r]}]
							]],Listable];
			,
			{\[Psi]up,d\[Psi]up}={X,Y}/.First@NDSolve[eqinf,{X,Y},{r,r2g,rout},Method->"StiffnessSwitching",WorkingPrecision->workODE,PrecisionGoal->precGoal,AccuracyGoal->accGoal,InterpolationOrder->intorder];

			Rup=Function[{r},Evaluate[If[r>rout,Evaluate[resfac[1,r]\[Psi]inf[r]],Evaluate[resfac[1,r]\[Psi]up[r]]]],Listable];
			dRup=Function[{r},Evaluate[If[r>rout,Evaluate[resfac[1,r](dfacexp[1,r]\[Psi]inf[r]+\[Psi]inf'[r])],Evaluate[resfac[1,r](dfacexp[1,r]\[Psi]up[r]+d\[Psi]up[r])]]],Listable];
		]
	];
	(* Remove local variables not garbage collected*)
	ClearSystemCache[];
	Remove[Evaluate[ToExpression[Pick[Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],StringMatchQ[#,"HSCSolverHomogeneousRadialTeukolsky`Private`X$"~~__]&/@Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],True]]]];
	Remove[Evaluate[ToExpression[Pick[Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],StringMatchQ[#,"HSCSolverHomogeneousRadialTeukolsky`Private`Y$"~~__]&/@Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],True]]]];
	Remove[r];

	{Rup,dRup,{rin,rout}}
]


(* ::Subsubsection::Closed:: *)
(*Up solution near the horizon*)


TsolverUpNearHorizon[s_,l_,m_,a_,\[Omega]_,\[Lambda]_,{\[Psi]up_,d\[Psi]up_}]:=Module[{precBC,rin,rout,rinplus,rinmin,rp,rm,\[Kappa],\[CapitalOmega]H,resfac,dfacexp,\[Psi]inf,cOutinf,nmaxinf,eqinf,r,rtor,\[Alpha],X,Y,cInHplus,cInHmin,nmaxhorplus,nmaxhormin,\[Psi]horplus,\[Psi]hormin,Cref,Cinc,Rhorplus,dRhorplus,Rhormin,dRhormin,C1,C2},
	rp=1+Sqrt[1-a^2];
	rm=1-Sqrt[1-a^2];
	\[Kappa]=\[Omega]-m*\[CapitalOmega]H;
	\[CapitalOmega]H=a/(2rp);
	rtor=Evaluate[(2rp)/(rp-rm) Log[(#-rp)/2]-(2rm)/(rp-rm) Log[(#-rm)/2]+#]&;
	\[Alpha]=rp*Exp[I*a*m(1/2+1/rp Log[(rp-rm)/2])];
	resfac=Evaluate[Function[{H,r},1/r (r^2-2r+a^2)^(-s)Exp[H*I*\[Omega]*rtor[r]]Exp[I*m*a/(rp-rm)(Log[(r-rp)/(r-rm)])]]];
	dfacexp=Function[{H,r},-(1/r +(2s(r-1))/(r^2-2r+a^2))+I/(r^2-2r+a^2) (H(r^2+a^2)\[Omega]+a m)];

	If[(Precision[a]==MachinePrecision)||(Precision[\[Omega]]==MachinePrecision)||(Precision[\[Lambda]]==MachinePrecision),
		precBC=15;
		,
		precBC=Min[{Precision[a],Precision[\[Omega]],Precision[\[Lambda]]}];
	];

	{cOutinf,rout}=bcinfplus[precBC,s,m,a,\[Omega],\[Lambda]];
	nmaxinf=Length[cOutinf];
	\[Psi]inf=Evaluate[Sum[cOutinf[[i]]#^(-i+1),{i,nmaxinf}]]&;

	{cInHplus,rinplus}=bchorplus[precBC,s,m,a,\[Omega],\[Lambda]];
	{cInHmin,rinmin}=bchormin[precBC,s,m,a,\[Omega],\[Lambda]];
	nmaxhorplus=Length[cInHplus];
	nmaxhormin=Length[cInHmin];
	rin=Max[{rinplus,rinmin}];

	\[Psi]horplus=Evaluate[Sum[cInHplus[[i]](#-rp)^(i-1),{i,nmaxhorplus}]]&;
	\[Psi]hormin=Evaluate[Sum[cInHmin[[i]](#-rp)^(i-1),{i,nmaxhormin}]]&;

	Rhorplus=Evaluate[Exp[I*\[Kappa]*rtor[#]]\[Psi]horplus[#]]&;
	dRhorplus=Evaluate[Rhorplus[#] (I*\[Kappa](a^2+#^2))/((#-rm)(#-rp))+Exp[I*\[Kappa]*rtor[#]]\[Psi]horplus'[#]]&;
	Rhormin=Evaluate[\[Alpha]*resfac[-1,#]\[Psi]hormin[#]]&;
	dRhormin=Evaluate[Rhormin[#] dfacexp[-1,#]+\[Alpha]*resfac[-1,#]\[Psi]hormin'[#]]&;

	{Cinc,Cref}={C1,C2}/.NSolve[C1 Rhorplus[rin]+C2 Rhormin[rin]==(resfac[1,rin]\[Psi]up[rin])&&C1 dRhorplus[rin]+C2 dRhormin[rin]==(resfac[1,rin](dfacexp[1,rin]\[Psi]up[rin]+d\[Psi]up[rin])),{C1,C2}][[1]];

	{
		{Function[{r},Evaluate[Cinc*Rhorplus[r]],Listable],Function[{r},Evaluate[Cinc* dRhorplus[r]],Listable]},
		{Function[{r},Evaluate[Cref*Rhormin[r]],Listable],Function[{r},Evaluate[Cref*dRhormin[r]],Listable]},
		{rin,rout},{Cinc,Cref}
	}
]


(* ::Section::Closed:: *)
(*Functions for BCs and Teukolsky solver in HS coordinates  - expansion in the secondary spin*)


(* ::Subsection::Closed:: *)
(*Boundary condition at the horizon - minus solution, secondary spin*)


bchormin1spin[workingprecision_,s_,m_,a_,\[Omega]0_,\[Omega]1_,\[Lambda]0_,\[Lambda]1_]:=Module[{M=1,deltarp,An0,rp,rm,rin,err,errold,i,chor0,chor1,p,q,phor0,qhor0,dphor0,dphor1,dqhor0,dqhor1,\[Psi]hor0,an0,an1,cInHor0,cInHor1},
	rp=M+Sqrt[M^2-a^2];
	rm=M-Sqrt[M^2-a^2];deltarp=(rp-rm)/50;
	rin=rp+deltarp; (*Closest r to the horizon *)
	chor0=2I (2M*rp)/(rp-rm)(\[Omega]0-(a*m)/(2M*rp))+s;
	chor1=(4I*M*rp*\[Omega]1)/(rp-rm);

	dqhor0[n_]:=Which[
					n==0,
					0,
					n==1,
					(2I*a*m+2M(-1+s)-2I*a^2*\[Omega]0+rp(2+\[Lambda]0-4I*rp*s*\[Omega]0))/((rm-rp)rp),
					n>1,
					2(-1+n)(-rp)^(-n)+(rm-rp)^(-n)(2+\[Lambda]0-4*I*rm*s*\[Omega]0)+1/rp 2n (rm-rp)^(-n)(M(-1+s)+I*a(m-a*\[Omega]0))(1+(1/n)*Sum[Binomial[n,k](-rm)^(k-1)/rp^(k-1),{k,2,n}])
				];

	dqhor1[n_]:=Which[
					n==0,
					0,
					n==1,
					(-2I*a^2*\[Omega]1+rp(\[Lambda]1-4I*rp*s*\[Omega]1))/((rm-rp)rp),
					n>1,
					1/rp(rm-rp)^(-n)(rp*\[Lambda]1-4I*a^2*s*\[Omega]1-2I*a^2*n*\[Omega]1*Hypergeometric2F1[1,1-n,2,rm/rp])
				];
	dphor0[n_]:=Which[
					n==0,
					1-chor0,
					n==1,
					 1/(rp (rm-rp)^2)(-2rm^2+a^2(3+2s+4I*rp*\[Omega]0)+I*rp(-2a*m+2a^2\[Omega]0+I(rp+2M*s+2I*rp^2*\[Omega]0))),
					n>1,
					2(-rp)^(-n)-(rm-rp)^(-n)+(rm-rp)^(-1-n)(rm (+2s)+2I*rm^2\[Omega]0+2I(-a*m+I*M*s+a^2\[Omega]0))
				];
	
	dphor1[n_]:=Which[
					n==0,
					-chor1,
					n==1,
					-((2I(-3a^2+rp^2)\[Omega]1)/(rm-rp)^2),
					n>1,
					2I(a^2+rm^2)(rm-rp)^(-1-n)\[Omega]1
				];
	
	an0[0]=1;
	An0[n_]:= -(1/(n(n-chor0)))Sum[(j*dphor0[n-j]+dqhor0[n-j])an0[j],{j,0,n-1}];
	
	err=1;
	errold=1;
	i=1;
	{p,q}=TeukolskyHSCoefficients;
	phor0=p[rin,-1,s,m,a,\[Omega]0,\[Lambda]0];
	qhor0=q[rin,-1,s,m,a,\[Omega]0,\[Lambda]0];
	
	While[err > 10^(-workingprecision),
		If[Mod[i,30]==0,
			deltarp=deltarp/2;
			rin=rp+deltarp;
			phor0=p[rin,-1,s,m,a,\[Omega]0,\[Lambda]0];
			qhor0=q[rin,-1,s,m,a,\[Omega]0,\[Lambda]0];
		];
	an0[i]=An0[i];
	\[Psi]hor0=Evaluate[1+Sum[an0[k](#-rp)^k,{k,i}]]&;
	err=Abs[\[Psi]hor0''[rin]+phor0 \[Psi]hor0'[rin]+qhor0 \[Psi]hor0[rin]];
	   
	   If[errold<=err&&errold> 10^(-workingprecision)&&i>5,
			Break[];
			,
			errold=err;
		];
		i++;
		
		If[i > 100, Break[]]  (*Safeguard to avoid ruwaway computation*)  
	];
	an1[0]=0;
	an1[n_]:=an1[n]=-(1/(n(n-chor0)))Sum[(chor1 /(n-chor0) an0[j]+ an1[j]) (j dphor0[n-j]+dqhor0[n-j])+ (j dphor1[-j+n]+dqhor1[-j+n])an0[j],{j,0,n-1}];

	cInHor0=Table[an0[k],{k,0,i-1}]; (*Coefficients for ingoing waves near horizon (-)*)
	cInHor1=Table[an1[k],{k,0,i-1}]; (*Coefficients for ingoing waves near horizon (-)*)

	(* Remove local variables not garbage collected*)
	Remove[dphor0,dqhor0,dphor1,dqhor1,an0,an1];

	{cInHor0,cInHor1,rin}
]


(* ::Subsection::Closed:: *)
(*Boundary condition at infinity - plus solution, secondary spin*)


bcinfplus1spin[workingprecision_,s_,m_,a_,\[Omega]0_,\[Omega]1_,\[Lambda]0_,\[Lambda]1_]:=Module[{M=1,rp,rm,rout,err,i,p,q,pinf0,qinf0,dpinf0,dpinf1,dqinf0,dqinf1,\[Psi]inf0,bn0,bn1,Bn0,cOutinf0,cOutinf1},
	rp=M+Sqrt[M^2-a^2];
	rm=M-Sqrt[M^2-a^2];
	rout=2\[Pi](1/Abs[\[Omega]0]+Abs[\[Omega]0]/(1+Abs[\[Omega]0]));

	dqinf0[n_]:=Which[
					n==0,
					0,
					n==1,
					0,
					n==2,
					-(4a*m*\[Omega]0+4*I*M*s*\[Omega]0+\[Lambda]0),
					n>2,
					1/(rm-rp)^3((rm-rp)^2(2rm^(-2+n)rp-2rm rp^(-2+n)+2I*a*m(-rm^(-2+n)+rp^(-2+n))+2M(-rm^(-2+n)+rp^(-2+n))(1+s)+(-rm^(-1+n)+rp^(-1+n))\[Lambda]0)+2I (rm-rp)^2(-rm^(-1+n)rp+rm*rp^(-1+n))\[Omega]0+4(a*m(-rp^n(2M+n*rm-n*rp)+rm^n(2M-n*rm+n*rp)+a^2(rp^(-2+n)(rm-n*rm+(-3+n)rp)+rm^(-2+n)(-(-3+n)rm+(-1+n)rp)))+I*M(-rp^n(2M+n*rm-n*rp)+rm^n(2M-n*rm+n*rp)+a^2(rp^(-2+n)((-1+n)rm-(-3+n)rp)+rm^(-2+n)((-3+n)*rm+rp-n*rp)))s)\[Omega]0)
				];

	dqinf1[n_]:=Which[
					n==0,
					0,
					n==1,
					0,
					n==2,
					-\[Lambda]1-4(a*m+I*M*s)\[Omega]1,
					n>2,
					1/(rm-rp)^3((rm-rp)^2(-rm^(-1+n)+rp^(-1+n))\[Lambda]1+2I (rm-rp)^2(-rm^(-1+n)rp+rm*rp^(-1+n))\[Omega]1+4a*m(rp^n(-2M+n(-rm+rp))+rm^n(2 M+n(-rm+rp))+a^2(rp^(-2+n)(rm-n*rm+(-3+n)rp)+rm^(-2+n)(-(-3+n)rm+(-1+n)rp)))\[Omega]1+4I*M(rp^n(-2M+n(-rm+rp))+rm^n(2M+n(-rm+rp))+a^2(rp^(-2+n)((-1+n) rm-(-3+n)rp)+rm^(-2+n)((-3+n)rm+rp-n*rp)))s*\[Omega]1)
				];

	dpinf0[n_]:=Which[
					n==0,
					2I*\[Omega]0,
					n==1,
					-2s+2I*2M*\[Omega]0 ,
					n>1,
					rm^(-1+n)+rp^(-1+n)+(2 rm^(-1+n)((M-rm)s+I(a*m+(a^2+rm^2)\[Omega]0)))/(rm-rp)-(2rp^(-1+n)((M-rp)s+I(a*m+(a^2+rp^2)\[Omega]0)))/(rm-rp)
				];

	dpinf1[n_]:=Which[
					n==0,
					2I*\[Omega]1,
					n==1,
					4I*M*\[Omega]1,
					n>1,
					(4I*M(rm^n -rp^n)\[Omega]1)/(rm-rp)
				];

	err=1;
	i=1;
	bn0[0]=1;
	Bn0[n_]:=(n-1)/(2I*\[Omega]0 ) bn0[n-1]+1/(2I*\[Omega]0*n) Sum[(dqinf0[j+1]-(n-j)dpinf0[j])bn0[n-j],{j,1,n}];

	{p,q}=TeukolskyHSCoefficients;
	pinf0=p[rout,1,s,m,a,\[Omega]0,\[Lambda]0];
	qinf0=q[rout,1,s,m,a,\[Omega]0,\[Lambda]0];

	While[err > 10^(-workingprecision),
		If[Mod[i,15]==0,
			rout=2rout;
			pinf0=p[rout,1,s,m,a,\[Omega]0,\[Lambda]0];
			qinf0=q[rout,1,s,m,a,\[Omega]0,\[Lambda]0];
		];
        bn0[i]=Bn0[i];
		\[Psi]inf0=Evaluate[1+Sum[bn0[k](#)^(-k),{k,i}]]&;
		err=Abs[\[Psi]inf0''[rout]+pinf0 \[Psi]inf0'[rout]+qinf0 \[Psi]inf0[rout]];
        i++;
		If[i > 150, Break[]]  (*Asymptotic expansions are not convergent*)    
	];
	bn1[0]=0;bn1[n_]:=bn1[n]=(n-1)/(2I*\[Omega]0)(bn1[n-1]-\[Omega]1/\[Omega]0 bn0[n-1])+1/(2I*\[Omega]0*n)Sum[(bn1[n-j]-\[Omega]1/\[Omega]0 bn0[n-j])(dqinf0[j+1]-(n-j)dpinf0[j])+(dqinf1[j+1]-(n-j)dpinf1[j])bn0[n-j],{j,1,n}];

	cOutinf0=Table[bn0[k],{k,0,i-1}]; (*Coefficients for outgoing waves at \[Infinity] (+)*)
	cOutinf1=Table[bn1[k],{k,0,i-1}];

	(* Remove local variables not garbage collected*)
	Remove[dpinf0,dqinf0,dpinf1,dqinf1,bn0,bn1];

	{cOutinf0,cOutinf1,rout}
]


(* ::Subsection::Closed:: *)
(*Teukolsky solver in hyperboloidal slicing coordinates*)


(* ::Subsubsection::Closed:: *)
(*In solution*)


TsolverIn1spin[s_,l_,m_,a_,\[Omega]0_,\[Omega]1_,\[Lambda]0_,\[Lambda]1_,r1g_,intorder_]:=Module[{workODE,precBC,precGoal,accGoal,r,rin,rtor,rp,rm,resfac,dfacexp0,dfacexp1,p0,p1,q0,q1,cInH0,cInH1,\[Psi]hor0,\[Psi]hor1,eqhor,\[Alpha],X0,Y0,X1,Y1,\[Psi]in0,d\[Psi]in0,\[Psi]in1,d\[Psi]in1,nmaxhor},
	rp = 1+Sqrt[1^2-a^2];
	rm = 1-Sqrt[1^2-a^2];
	rtor=Evaluate[(2rp)/(rp-rm) Log[(#-rp)/2]-(2rm)/(rp-rm) Log[(#-rm)/2]+#]&;
	\[Alpha]=rp*Exp[I*a*m(1/2+1/rp Log[(rp-rm)/2])];
	resfac=Evaluate[Function[{H,r},1/r*(r^2-2r+a^2)^(-s)Exp[H*I*\[Omega]0*rtor[r]]Exp[I*m*a/(rp-rm)(Log[(r-rp)/(r-rm)])]]];
	dfacexp0=Function[{H,r},-(1/r +(2s(r-1))/(r^2-2r+a^2))+I/(r^2-2r+a^2) (H*(r^2+a^2)\[Omega]0+a m)];
	dfacexp1=Function[{H,r},I*H*\[Omega]1((r^2+a^2)/(r^2-2r+a^2)+rtor[r] dfacexp0[H,r])];

	If[(Precision[a]==MachinePrecision)||(Precision[\[Omega]0]==MachinePrecision)||(Precision[\[Lambda]0]==MachinePrecision)||(Precision[\[Omega]1]==MachinePrecision)||(Precision[\[Lambda]1]==MachinePrecision)||(Precision[r1g]==MachinePrecision),
		workODE=MachinePrecision;
		precGoal=13;
		accGoal=13;
		precBC=15;
		,
		workODE=Min[{Precision[a]-5,Precision[\[Omega]0]-5,Precision[\[Lambda]0]-5,Precision[\[Omega]1]-5,Precision[\[Lambda]1]-5,Precision[r1g]-5}];
		precGoal=workODE-5;
		accGoal=workODE-5;
		precBC=Min[{Precision[a],Precision[\[Omega]0],Precision[\[Lambda]0],Precision[\[Omega]1],Precision[\[Lambda]1],Precision[r1g]}];
	];

	{p0,q0}=TeukolskyHSCoefficients;
	{p1,q1}=TeukolskyHSCoefficients1spin;

	{cInH0,cInH1,rin}=bchormin1spin[precBC,s,m,a,\[Omega]0,\[Omega]1,\[Lambda]0,\[Lambda]1];

	nmaxhor=Length[cInH0];
	\[Psi]hor0=Evaluate[Sum[cInH0[[i]](#-rp)^(i-1),{i,nmaxhor}]]&;
	\[Psi]hor1=Evaluate[Sum[cInH1[[i]](#-rp)^(i-1),{i,nmaxhor}]]&;

	eqhor={
		X0'[r] == Y0[r],
		Y0'[r] == -p0[r,-1,s,m,a,\[Omega]0,\[Lambda]0]Y0[r]-q0[r,-1,s,m,a,\[Omega]0,\[Lambda]0] X0[r],
		X1'[r] == Y1[r],Y1'[r] == -(p0[r,-1,s,m,a,\[Omega]0,\[Lambda]0]Y1[r]+q0[r,-1,s,m,a,\[Omega]0,\[Lambda]0] X1[r])-(p1[r,-1,s,m,a,\[Omega]0,\[Omega]1,\[Lambda]0,\[Lambda]1]Y0[r]+q1[r,-1,s,m,a,\[Omega]0,\[Omega]1,\[Lambda]0,\[Lambda]1] X0[r]),
		X0[rin] == \[Psi]hor0[rin],Y0[rin] == \[Psi]hor0'[rin],X1[rin] == \[Psi]hor1[rin],Y1[rin] == \[Psi]hor1'[rin]
	};

	{\[Psi]in0,d\[Psi]in0,\[Psi]in1,d\[Psi]in1} = {X0,Y0,X1,Y1}/.First@NDSolve[eqhor,{X0,Y0,X1,Y1},{r,rin,r1g},Method->"StiffnessSwitching",WorkingPrecision->workODE,PrecisionGoal->precGoal,AccuracyGoal->accGoal,InterpolationOrder->intorder];

	(* Remove local variables not garbage collected*)
	ClearSystemCache[];
	Remove[Evaluate[ToExpression[Pick[Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],StringMatchQ[#,"HSCSolverHomogeneousRadialTeukolsky`Private`X0$"~~__]&/@Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],True]]]];
	Remove[Evaluate[ToExpression[Pick[Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],StringMatchQ[#,"HSCSolverHomogeneousRadialTeukolsky`Private`Y0$"~~__]&/@Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],True]]]];
	Remove[Evaluate[ToExpression[Pick[Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],StringMatchQ[#,"HSCSolverHomogeneousRadialTeukolsky`Private`X1$"~~__]&/@Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],True]]]];
	Remove[Evaluate[ToExpression[Pick[Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],StringMatchQ[#,"HSCSolverHomogeneousRadialTeukolsky`Private`Y1$"~~__]&/@Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],True]]]];
	Remove[r];

	{Function[{r},Evaluate[If[r<=rin,Evaluate[\[Alpha]*resfac[-1,r]\[Psi]hor0[r]],Evaluate[\[Alpha]*resfac[-1,r]\[Psi]in0[r]]]],Listable],
	Function[{r},Evaluate[If[r<=rin,Evaluate[\[Alpha]*resfac[-1,r](dfacexp0[-1,r]\[Psi]hor0[r]+\[Psi]hor0'[r])],Evaluate[\[Alpha]*resfac[-1,r](dfacexp0[-1,r]\[Psi]in0[r]+d\[Psi]in0[r])]]],Listable],
	Function[{r},Evaluate[
						If[r<=rin,
							Evaluate[\[Alpha]*resfac[-1,r](\[Psi]hor1[r]-I*rtor[r]*\[Omega]1*\[Psi]hor0[r])],
							Evaluate[\[Alpha]*resfac[-1,r](\[Psi]in1[r]-I*rtor[r]*\[Omega]1*\[Psi]in0[r])]]
						],Listable],
	Function[{r},Evaluate[
						If[r<=rin,
							Evaluate[\[Alpha]*resfac[-1,r](\[Psi]in1[r] dfacexp0[-1,r]+\[Psi]in0[r] dfacexp1[-1,r]+d\[Psi]in1[r]-I*rtor[r]*\[Omega]1*d\[Psi]in0[r])],
							Evaluate[\[Alpha]*resfac[-1,r](\[Psi]in1[r] dfacexp0[-1,r]+\[Psi]in0[r] dfacexp1[-1,r]+d\[Psi]in1[r]-I*rtor[r]*\[Omega]1*d\[Psi]in0[r])]]
						],Listable]
	,rin}
]


(* ::Subsubsection::Closed:: *)
(*Up solution*)


TsolverUp1spin[s_,l_,m_,a_,\[Omega]0_,\[Omega]1_,\[Lambda]0_,\[Lambda]1_,r2g_,intorder_]:=Module[{workODE,precBC,precGoal,accGoal,r,rout,rtor,rp,rm,resfac,dfacexp0,dfacexp1,p0,p1,q0,q1,cOutinf0,cOutinf1,\[Psi]inf0,\[Psi]inf1,eqinf,\[Alpha],X0,Y0,X1,Y1,\[Psi]up0,d\[Psi]up0,\[Psi]up1,d\[Psi]up1,nmaxinf},
	rp = 1+Sqrt[1^2-a^2];
	rm = 1-Sqrt[1^2-a^2];
	rtor=Evaluate[(2rp)/(rp-rm) Log[(#-rp)/2]-(2rm)/(rp-rm) Log[(#-rm)/2]+#]&;
	\[Alpha]=rp*Exp[I*a*m(1/2+1/rp Log[(rp-rm)/2])];
	resfac=Evaluate[Function[{H,r},1/r*(r^2-2r+a^2)^(-s)Exp[H*I*\[Omega]0*rtor[r]]Exp[I*m*a/(rp-rm)(Log[(r-rp)/(r-rm)])]]];
	dfacexp0=Function[{H,r},-(1/r +(2s(r-1))/(r^2-2r+a^2))+I/(r^2-2r+a^2) (H*(r^2+a^2)\[Omega]0+a m)];
	dfacexp1=Function[{H,r},I*H*\[Omega]1((r^2+a^2)/(r^2-2r+a^2)+rtor[r] dfacexp0[H,r])];

	If[(Precision[a]==MachinePrecision)||(Precision[\[Omega]0]==MachinePrecision)||(Precision[\[Lambda]0]==MachinePrecision)||(Precision[\[Omega]1]==MachinePrecision)||(Precision[\[Lambda]1]==MachinePrecision)||(Precision[r2g]==MachinePrecision),
		workODE=MachinePrecision;
		precGoal=13;
		accGoal=13;
		precBC=15;
		,
		workODE=Min[{Precision[a]-5,Precision[\[Omega]0]-5,Precision[\[Lambda]0]-5,Precision[\[Omega]1]-5,Precision[\[Lambda]1]-5,Precision[r2g]-5}];
		precGoal=workODE-5;
		accGoal=workODE-5;
		precBC=Min[{Precision[a],Precision[\[Omega]0],Precision[\[Lambda]0],Precision[\[Omega]1],Precision[\[Lambda]1],Precision[r2g]}];
	];


	{p0,q0}=TeukolskyHSCoefficients;
	{p1,q1}=TeukolskyHSCoefficients1spin;

	{cOutinf0,cOutinf1,rout}=bcinfplus1spin[precBC,s,m,a,\[Omega]0,\[Omega]1,\[Lambda]0,\[Lambda]1];
	nmaxinf = Length[cOutinf0];
	\[Psi]inf0=Evaluate[Sum[cOutinf0[[i]]#^(-i+1),{i,nmaxinf}]]&;
	\[Psi]inf1=Evaluate[Sum[cOutinf1[[i]]#^(-i+1),{i,nmaxinf}]]&;

	eqinf={
		X0'[r] == Y0[r],
		Y0'[r] == -p0[r,1,s,m,a,\[Omega]0,\[Lambda]0]Y0[r]-q0[r,1,s,m,a,\[Omega]0,\[Lambda]0] X0[r],
		X1'[r] == Y1[r],
		Y1'[r] == -(p0[r,1,s,m,a,\[Omega]0,\[Lambda]0] Y1[r]+q0[r,1,s,m,a,\[Omega]0,\[Lambda]0] X1[r])-(p1[r,1,s,m,a,\[Omega]0,\[Omega]1,\[Lambda]0,\[Lambda]1] Y0[r]+q1[r,1,s,m,a,\[Omega]0,\[Omega]1,\[Lambda]0,\[Lambda]1] X0[r]),
		X0[rout] == \[Psi]inf0[rout],Y0[rout] == \[Psi]inf0'[rout],X1[rout] == \[Psi]inf1[rout],Y1[rout] == \[Psi]inf1'[rout]
		};
	{\[Psi]up0,d\[Psi]up0,\[Psi]up1,d\[Psi]up1} = {X0,Y0,X1,Y1}/.First@NDSolve[eqinf,{X0,Y0,X1,Y1},{r,r2g,rout},Method->"StiffnessSwitching",WorkingPrecision->workODE,PrecisionGoal->precGoal,AccuracyGoal->accGoal,InterpolationOrder->intorder];
  
   (* Remove local variables not garbage collected*)
	ClearSystemCache[];
	Remove[Evaluate[ToExpression[Pick[Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],StringMatchQ[#,"HSCSolverHomogeneousRadialTeukolsky`Private`X0$"~~__]&/@Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],True]]]];
	Remove[Evaluate[ToExpression[Pick[Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],StringMatchQ[#,"HSCSolverHomogeneousRadialTeukolsky`Private`Y0$"~~__]&/@Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],True]]]];
	Remove[Evaluate[ToExpression[Pick[Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],StringMatchQ[#,"HSCSolverHomogeneousRadialTeukolsky`Private`X1$"~~__]&/@Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],True]]]];
	Remove[Evaluate[ToExpression[Pick[Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],StringMatchQ[#,"HSCSolverHomogeneousRadialTeukolsky`Private`Y1$"~~__]&/@Names["HSCSolverHomogeneousRadialTeukolsky`Private`*"],True]]]];
	Remove[r];

	{Function[{r},Evaluate[If[r>rout,Evaluate[resfac[1,r]\[Psi]inf0[r]],Evaluate[resfac[1,r]\[Psi]up0[r]] ]],Listable],
	Function[{r},Evaluate[If[r>rout,Evaluate[resfac[1,r](dfacexp0[1,r]\[Psi]inf0[r]+\[Psi]inf0'[r])],Evaluate[resfac[1,r](dfacexp0[1,r]\[Psi]up0[r]+d\[Psi]up0[r])]]],Listable],
	Function[{r},Evaluate[
						If[r>=rout,
							Evaluate[resfac[1,r](\[Psi]inf1[r]+I*rtor[r]*\[Omega]1*\[Psi]inf0[r])],
							Evaluate[resfac[1,r](\[Psi]up1[r]+I*rtor[r]*\[Omega]1*\[Psi]up0[r])]]
						],Listable],
	Function[{r},Evaluate[
						If[r>=rout,
							Evaluate[resfac[1,r](\[Psi]inf1[r] dfacexp0[1,r]+\[Psi]inf0[r] dfacexp1[1,r]+\[Psi]inf1'[r]+I*rtor[r]*\[Omega]1*\[Psi]inf0'[r])],
							Evaluate[resfac[1,r](\[Psi]up1[r] dfacexp0[1,r]+\[Psi]up0[r] dfacexp1[1,r]+d\[Psi]up1[r]+I*rtor[r]*\[Omega]1*d\[Psi]up0[r])]]
						],Listable]
	,rout}
]


(* ::Section::Closed:: *)
(*End package*)


End[];


EndPackage[];
