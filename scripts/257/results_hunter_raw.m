Q := Rationals();
R<t> := PolynomialRing(Q);

pols := [
	//1247
	t^8 + 4*t^7 - 70*t^5 + 245*t^4 + 574*t^3 - 2254*t^2 - 4880*t - 2370,
    t^8 + 4*t^7 + 560*t^4 + 2800*t^3 + 5600*t^2 + 1600*t - 2000,
    t^8 + 4*t^7 + 28*t^6 + 70*t^5 + 525*t^4 + 938*t^3 - 1778*t^2 - 2236*t - 670,
    t^8 + 4*t^7 + 28*t^6 + 252*t^5 + 924*t^4 + 952*t^3 - 952*t^2 - 3176*t - 244,
    t^8 + 4*t^7 - 28*t^5 + 490*t^4 - 644*t^3 + 504*t^2 + 3420*t - 243,
    t^8 + 4*t^7 + 42*t^5 + 525*t^4 + 1022*t^3 - 1862*t^2 - 40*t - 6,
    t^8 + 4*t^7 - 28*t^6 - 168*t^5 + 140*t^4 + 1680*t^3 + 1120*t^2 - 1600*t + 2000,
    t^8 + 2*t^7 - 14*t^6 - 70*t^5 - 245*t^4 - 700*t^3 - 1400*t^2 - 3000*t - 2500,
    t^8 + 2*t^7 + 84*t^5 - 105*t^4 + 126*t^3 - 938*t^2 - 1100*t - 1346,
    t^8 + 2*t^7 - 14*t^6 - 84*t^5 + 126*t^4 - 1960*t^3 + 2184*t^2 - 960*t - 520,
    t^8 + 2*t^7 + 28*t^6 - 56*t^5 - 385*t^4 - 1022*t^3 - 1554*t^2 - 516*t - 178,
    t^8 + 2*t^7 - 14*t^6 - 28*t^5 + 70*t^4 - 112*t^3 + 56*t^2 - 112*t + 56,
    t^8 + 2*t^7 + 14*t^6 + 168*t^5 + 210*t^4 + 672*t^3 + 224*t^2 + 128*t + 256,
    t^8 + 2*t^7 + 70*t^5 + 280*t^4 + 462*t^3 - 196*t^2 + 410*t + 435,
    t^8 + 2*t^7 + 14*t^6 - 14*t^5 + 399*t^4 - 2268*t^3 + 3136*t^2 - 1480*t + 540,
    t^8 + 2*t^7 + 14*t^6 + 98*t^5 + 175*t^4 + 336*t^3 + 2492*t^2 + 4664*t + 1768,
    t^8 + 2*t^7 - 28*t^6 - 140*t^5 + 35*t^4 + 1638*t^3 + 5166*t^2 + 6316*t + 2650,
    t^8 + 14*t^6 + 21*t^4 - 196*t^2 - 200*t - 504,
    t^8 + 14*t^6 + 21*t^4 - 196*t^2 + 200*t - 504,
    t^8 - 490*t^4 + 672*t^3 + 1680*t^2 + 2400*t + 665,
    t^8 - 490*t^4 - 672*t^3 + 1680*t^2 - 2400*t + 665,
    t^8 - 28*t^6 + 126*t^4 + 2240*t^3 + 3220*t^2 - 1600*t + 1225,
    t^8 - 28*t^6 + 126*t^4 - 2240*t^3 + 3220*t^2 + 1600*t + 1225,
    //1265
    t^8 + 4*t^7 + 2*t^6 - 28*t^5 - 35*t^4 + 448*t^3 + 532*t^2 - 2744*t - 3864,
    t^8 + 4*t^7 + 2*t^6 + 12*t^5 + 65*t^4 - 352*t^3 - 768*t^2 + 2456*t - 1044,
    t^8 + 4*t^7 - 18*t^6 - 68*t^5 + 125*t^4 + 368*t^3 - 128*t^2 - 1024*t - 1024,
    t^8 + 4*t^7 - 18*t^6 - 68*t^5 + 125*t^4 + 368*t^3 - 128*t^2 + 376*t - 324,
    t^8 + 4*t^7 - 28*t^5 + 70*t^4 + 476*t^3 + 784*t^2 - 260*t - 263,
    t^8 + 4*t^7 - 28*t^6 - 168*t^5 - 280*t^4 - 392*t^3 - 448*t^2 + 656*t - 204,
    t^8 + 4*t^7 + 140*t^4 + 800*t + 400,
    t^8 + 2*t^7 - 2*t^6 - 66*t^5 + 195*t^4 - 656*t^3 - 32*t^2 - 928*t - 964,
    t^8 + 2*t^7 + 28*t^6 - 56*t^5 + 595*t^4 + 294*t^3 - 1582*t^2 - 808*t - 174,
    t^8 + 2*t^7 + 28*t^6 + 14*t^5 + 140*t^4 + 14*t^3 - 112*t^2 - 238*t - 49,
    t^8 + 12*t^6 - 72*t^5 + 250*t^4 - 464*t^3 + 180*t^2 - 808*t - 2347,
    t^8 - 12*t^6 - 64*t^5 - 10*t^4 + 768*t^3 + 1940*t^2 + 1344*t - 47,
    t^8 - 32*t^6 - 16*t^5 + 230*t^4 + 192*t^3 + 320*t^2 + 16*t + 73,
    t^8 - 20*t^6 - 50*t^5 - 55*t^4 - 50*t^3 + 50*t^2 + 50,
    t^8 + 8*t^6 - 96*t^5 + 270*t^4 - 608*t^3 + 520*t^2 + 576*t + 113,
    t^8 - 1600*t + 2800,
    t^8 + 1600*t + 2800,
    //1267
    t^8 + 4*t^7 + 42*t^6 + 112*t^5 + 595*t^4 + 1008*t^3 + 1162*t^2 + 676*t - 24799,
    t^8 + 4*t^7 - 168*t^5 - 1820*t^4 - 5488*t^3 - 10752*t^2 - 10400*t - 6096,
    t^8 + 4*t^7 + 140*t^5 + 350*t^4 - 196*t^3 - 784*t^2 - 780*t - 4415,
    t^8 + 4*t^7 + 140*t^5 - 770*t^4 + 4284*t^3 - 9744*t^2 + 5380*t - 915,
    t^8 + 4*t^7 - 224*t^3 - 896*t^2 - 1280*t - 640,
    t^8 + 4*t^7 - 28*t^6 - 28*t^5 + 70*t^4 + 308*t^3 + 3052*t^2 - 5644*t + 7741,
    t^8 + 4*t^7 + 112*t^5 + 560*t^4 + 1120*t^3 + 4480*t^2 - 21920*t + 16480,
    t^8 + 28*t^6 - 56*t^5 + 350*t^4 - 1456*t^3 + 2380*t^2 - 9688*t + 441,
    t^8 - 70*t^5 - 1575*t^4 + 350*t^3 + 28350*t^2 - 10500*t + 1750,
    //1447
    t^8 + 2*t^7 - 14*t^6 + 42*t^5 - 140*t^4 - 518*t^3 + 1274*t^2 + 4062*t - 8011,
    t^8 + 2*t^7 + 14*t^6 - 42*t^5 + 280*t^4 + 182*t^3 - 546*t^2 + 2018*t - 3419,
    t^8 + 2*t^7 - 308*t^3 - 1596*t^2 - 3260*t - 2950,
    t^8 + 2*t^7 - 14*t^6 - 70*t^5 - 140*t^4 + 3290*t^3 - 3850*t^2 + 1150*t + 25,
    t^8 + 2*t^7 - 280*t^4 - 1400*t^3 - 1400*t^2 + 800*t + 1250,
    t^8 + 2*t^7 + 28*t^6 - 56*t^5 + 560*t^4 + 588*t^3 - 1764*t^2 - 936*t + 1502,
    //1465
    t^8 + 4*t^7 + 560*t^4 + 2800*t^3 + 4480*t^2 + 1600*t - 2000,
    t^8 + 4*t^7 - 28*t^5 + 490*t^4 - 644*t^3 - 616*t^2 + 1180*t - 1363,
    //1467
    t^8 + 4*t^7 - 140*t^5 + 784*t^3 + 336*t^2 - 29200*t - 26920,
    t^8 + 4*t^7 - 168*t^5 + 560*t^4 - 4200*t^3 - 38920*t^2 - 31840*t - 8780,
    t^8 + 4*t^7 + 140*t^5 - 616*t^3 + 336*t^2 + 1040*t - 6760,
    t^8 + 4*t^7 - 896*t^3 - 3584*t^2 - 5120*t - 2560,
    t^8 + 4*t^7 + 280*t^5 - 560*t^4 + 1624*t^3 - 2184*t^2 - 4000*t - 1580,
    t^8 + 4*t^7 - 56*t^6 - 280*t^5 + 672*t^3 + 448*t^2 - 192*t - 320,
    t^8 + 4*t^7 - 140*t^5 - 560*t^4 - 56*t^3 + 5376*t^2 + 17840*t + 15640,
    t^8 + 28*t^6 - 84*t^5 - 2688*t^3 + 9520*t^2 + 416*t - 19208,
    t^8 - 28*t^6 - 112*t^5 + 2240*t^4 + 2576*t^3 + 5040*t^2 + 30112*t - 2352,
    t^8 - 28*t^6 - 112*t^5 + 112*t^3 + 560*t^2 + 544*t + 336,
    t^8 - 280*t^2 - 700,
    t^8 + 672*t^3 + 840*t^2 + 1120*t + 4900,
    t^8 - 672*t^3 + 840*t^2 - 1120*t + 4900,
    t^8 + 28*t^6 - 84*t^5 - 560*t^4 - 840*t^3 + 5600*t^2 + 800*t + 12600,
    t^8 - 140*t^5 - 840*t^3 + 1680*t^2 - 2800*t + 7000,
    t^8 + 2*t^7 + 28*t^6 + 84*t^5 + 560*t^4 + 2156*t^3 - 588*t^2 + 34888*t - 29106,
    t^8 + 2*t^7 + 28*t^6 + 224*t^5 - 840*t^4 - 2072*t^3 + 616*t^2 + 18924*t - 12258,
    t^8 + 2*t^7 - 56*t^5 - 140*t^4 - 644*t^3 - 1008*t^2 - 5220*t - 486,
    t^8 + 2*t^7 - 14*t^6 + 42*t^5 + 140*t^4 + 98*t^3 + 126*t^2 + 198*t + 81,
    t^8 + 2*t^7 - 14*t^6 - 98*t^5 - 280*t^4 - 1470*t^3 - 4550*t^2 - 3450*t + 2025,
    t^8 + 2*t^7 + 56*t^6 + 140*t^5 - 560*t^4 + 7504*t^3 + 26348*t^2 + 24204*t + 3510,
    t^8 + 2*t^7 + 140*t^5 - 700*t^4 - 2100*t^3 + 13300*t^2 - 18500*t + 6750,
    t^8 + 2*t^7 - 140*t^5 - 2772*t^3 + 6496*t^2 + 8660*t + 74790,
    t^8 + 2*t^7 + 28*t^6 + 84*t^5 - 504*t^3 - 1988*t^2 - 2692*t - 2906,
    t^8 + 2*t^7 + 56*t^6 - 168*t^5 - 1260*t^4 - 8204*t^3 - 7168*t^2 + 11016*t + 12862,
    t^8 + 2*t^7 - 14*t^6 - 70*t^5 - 980*t^4 - 7630*t^3 - 22330*t^2 - 18590*t + 13465,
    t^8 + 2*t^7 - 14*t^6 - 210*t^5 - 140*t^4 + 1890*t^3 + 8190*t^2 - 32450*t + 31105,
    t^8 + 2*t^7 - 14*t^6 - 70*t^5 - 420*t^4 - 2394*t^3 - 7798*t^2 - 13234*t - 9115,
    t^8 + 2*t^7 + 1092*t^3 - 3556*t^2 + 6400*t - 6730,
    t^8 + 2*t^7 + 280*t^5 - 1680*t^4 + 3752*t^3 - 2716*t^2 - 4940*t - 1690,
    t^8 + 2*t^7 - 14*t^6 - 70*t^5 - 140*t^4 + 770*t^3 + 1890*t^2 + 2130*t + 2405,
    t^8 + 2*t^7 + 28*t^6 + 84*t^5 - 756*t^3 - 2212*t^2 - 2968*t - 1554,
    t^8 + 2*t^7 - 14*t^6 - 98*t^5 + 280*t^4 + 1442*t^3 - 2926*t^2 - 6118*t + 11109,
    t^8 + 2*t^7 - 42*t^6 - 266*t^5 + 4662*t^3 + 17794*t^2 + 26906*t + 14493,
    t^8 + 2*t^7 - 140*t^5 - 700*t^4 + 1652*t^3 + 14084*t^2 - 14040*t - 49010,
    t^8 + 2*t^7 - 42*t^6 + 14*t^5 + 700*t^4 - 2786*t^3 + 2898*t^2 + 13022*t - 37859,
    t^8 + 2*t^7 + 224*t^5 - 560*t^4 + 3192*t^3 - 3976*t^2 + 13120*t - 12722,
    t^8 + 2*t^7 - 14*t^6 - 70*t^5 - 140*t^4 + 6650*t^3 - 20510*t^2 + 26210*t - 12155,
    t^8 + 2*t^7 - 14*t^6 - 70*t^5 + 140*t^4 + 630*t^3 - 630*t^2 - 4030*t - 5855,
    t^8 + 2*t^7 - 42*t^6 - 126*t^5 - 140*t^4 - 1582*t^3 - 2954*t^2 - 786*t - 3623,
    t^8 + 2*t^7 - 14*t^6 - 70*t^5 - 140*t^4 - 1750*t^3 - 12670*t^2 - 5150*t + 68485,
    t^8 + 2*t^7 + 84*t^5 - 700*t^4 - 2800*t^3 + 11760*t^2 + 18720*t - 61330,
    t^8 + 2*t^7 - 14*t^6 + 210*t^5 + 420*t^4 - 3570*t^3 + 10850*t^2 - 5430*t - 53455,
    t^8 + 2*t^7 - 42*t^6 - 126*t^5 + 1120*t^4 - 1106*t^3 + 518*t^2 - 838*t + 221,
    t^8 + 2*t^7 - 70*t^6 - 70*t^5 + 1680*t^4 + 2002*t^3 + 2254*t^2 + 27890*t + 725,
    t^8 + 2*t^7 - 14*t^6 - 70*t^5 + 630*t^3 - 910*t^2 + 3530*t + 725,
    t^8 + 2*t^7 - 42*t^6 + 14*t^5 + 1680*t^4 + 9674*t^3 + 8778*t^2 - 18338*t + 7781,
    t^8 + 2*t^7 - 14*t^6 - 210*t^5 + 1820*t^4 - 4802*t^3 + 4326*t^2 + 4118*t - 9075,
    t^8 + 2*t^7 + 70*t^6 + 154*t^5 + 2100*t^4 - 16926*t^3 - 84882*t^2 + 39110*t - 4359,
    t^8 + 2*t^7 - 14*t^6 + 70*t^5 - 140*t^4 - 882*t^3 - 2254*t^2 + 1298*t - 435,
    t^8 + 2*t^7 - 14*t^6 + 70*t^5 - 980*t^4 + 2422*t^3 + 6734*t^2 - 8258*t + 13605,
    t^8 + 2*t^7 - 868*t^3 - 6496*t^2 - 17680*t - 25490,
    t^8 + 2*t^7 + 70*t^6 + 210*t^5 + 980*t^4 + 3682*t^3 - 17626*t^2 + 18090*t - 6275,
    t^8 + 2*t^7 - 14*t^6 + 70*t^5 + 280*t^4 - 490*t^3 + 350*t^2 - 250*t + 25,
    t^8 + 2*t^7 + 672*t^3 + 2884*t^2 + 7100*t + 9790,
    t^8 + 2*t^7 - 280*t^5 - 1400*t^4 - 2968*t^3 - 756*t^2 - 1580*t + 9790,
    t^8 + 2*t^7 - 70*t^6 - 126*t^5 + 840*t^4 + 7210*t^3 + 10990*t^2 - 20230*t + 14245,
    t^8 + 2*t^7 - 42*t^6 - 126*t^5 + 140*t^4 + 714*t^3 + 11298*t^2 + 44662*t + 41101,
    t^8 + 2*t^7 - 14*t^6 + 182*t^5 + 1400*t^4 + 602*t^3 - 16366*t^2 - 56258*t - 65791,
    t^8 + 2*t^7 + 70*t^6 + 14*t^5 + 700*t^4 - 18774*t^3 - 25718*t^2 - 9070*t - 4231,
    t^8 + 2*t^7 + 364*t^5 - 2240*t^4 + 4564*t^3 - 4312*t^2 + 4100*t - 2314,
    t^8 + 2*t^7 - 308*t^3 - 336*t^2 + 6400*t - 2530,
    t^8 + 2*t^7 - 14*t^6 - 98*t^5 + 140*t^4 + 154*t^3 + 798*t^2 + 1274*t + 413,
    t^8 + 2*t^7 - 28*t^3 - 56*t^2 - 40*t - 10,
    t^8 + 2*t^7 + 140*t^5 + 392*t^3 - 336*t^2 + 100*t - 10,
    t^8 + 2*t^7 - 14*t^6 - 70*t^5 - 700*t^4 - 910*t^3 + 12250*t^2 + 27750*t + 10385,
    t^8 + 2*t^7 - 70*t^6 + 14*t^5 + 1260*t^4 - 3234*t^3 + 6902*t^2 - 29010*t + 33029,
    t^8 + 2*t^7 - 42*t^6 + 14*t^5 + 840*t^4 - 1806*t^3 - 8022*t^2 + 23662*t + 43901
];