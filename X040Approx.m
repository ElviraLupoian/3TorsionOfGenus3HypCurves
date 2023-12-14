// these are the complex approximations used to compute the 3-torsion of J0(40)

CC := ComplexField(2000) ;
im := CC.1 ;
e := Exp(1) ;
e := CC ! e ;

AP := [ [1.0 - 0.2960916932563543*im,	0.2898051278177868 + 1.7932470952360352*(e^-30)*im,	-7.420389744364426 + 0.5921833865127086*im,	-6.420389744364426 - 0.5921833865127086*im,	-2.4203897443644267 - 0.8882750797690631*im,	-0.2898051278177868 - 0.5921833865127086*im,	1.6924057816719806 - 0.27628683583830593*im,	1.0 + 4.979603980413933*e^(-30)*im,	0.30759421832801936 + 0.27628683583830593*im,	-6.840779488728853 - 1.1843667730254173*im], [-0.6371809755031661 + 1.7509799266456525*im,	-1.0 - 3.549874073494553*(e^-30)*im,	0.5826561236825946 - 4.608836233203803*im,	3.0 + 1.9721522630525295*(e^-29)*im,	0.6371809755031661 - 1.7509799266456525*im,	1.0 + 3.549874073494553*(e^-30)*im,	0.47013742326544533 + 1.4151261803376836*im,	-1.0 - 4.930380657631324*(e^-30)*im,	-1.3435287292045357*(e^-30) - 5.9164567891575885*(e^-31)*im,	-3.93213555666014 + 4.790166946757614*im], [4.641614965976127*(e^-31) - 2.3985639866206276*im,	1.0 - 2.3985639866206276*im,	-2.0 + 11.551792307131947*im,	-1.0 + 25.061120974913333*im,	2.0 + 22.662556988292707*im,	-1.0 + 9.153228320511321*im,	1.799337253940777 - 1.6161981171152555*im,	2.598674507881554 - 3.232396234230511*im,	1.799337253940777 - 1.6161981171152555*im,	-4.0 + 3.915072721298875*im]];