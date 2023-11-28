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
    t^8 + 4*t^7 - 168*t^5 - 840*t^4 + 2240*t^3 + 13440*t^2 - 10240*t - 58880,
    t^8 + 4*t^7 - 28*t^6 - 168*t^5 - 70*t^4 + 364*t^3 - 7084*t^2 - 34792*t - 52347,
    t^8 + 4*t^7 + 140*t^5 - 70*t^4 - 4004*t^3 + 3304*t^2 + 27860*t - 38115,
    t^8 + 4*t^7 - 56*t^6 - 224*t^5 + 630*t^4 + 3780*t^3 - 1960*t^2 - 29880*t - 36815,
    t^8 + 4*t^7 - 140*t^5 - 1960*t^4 - 3472*t^3 - 17528*t^2 - 36680*t - 29820,
    t^8 + 4*t^7 - 140*t^5 + 784*t^3 + 336*t^2 - 29200*t - 26920,
    t^8 + 4*t^7 - 28*t^6 - 28*t^5 + 280*t^4 + 392*t^3 - 7392*t^2 + 19904*t - 24936,
    t^8 + 4*t^7 - 168*t^5 - 840*t^4 - 5488*t^3 - 24192*t^2 - 36640*t - 18096,
    t^8 + 4*t^7 + 112*t^5 + 2450*t^4 + 3668*t^3 - 13048*t^2 - 30800*t - 16639,
    t^8 + 4*t^7 - 168*t^5 - 1260*t^4 - 18480*t^3 - 42000*t^2 - 34000*t - 16300,
    t^8 + 4*t^7 - 28*t^5 - 1960*t^4 - 336*t^3 - 28504*t^2 + 14040*t - 14652,
    t^8 + 4*t^7 - 28*t^6 - 308*t^5 - 1400*t^4 - 3752*t^3 - 1008*t^2 - 19744*t - 14184,
    t^8 + 4*t^7 - 56*t^6 - 140*t^5 + 840*t^4 - 224*t^3 - 8176*t^2 + 17904*t - 11880,
    t^8 + 4*t^7 + 140*t^5 + 1330*t^4 + 8036*t^3 - 21336*t^2 - 30340*t - 10935,
    t^8 + 4*t^7 + 112*t^5 - 1330*t^4 - 3052*t^3 - 17528*t^2 + 4880*t - 9019,
    t^8 + 4*t^7 - 168*t^5 + 560*t^4 - 4200*t^3 - 38920*t^2 - 31840*t - 8780,
    t^8 + 4*t^7 - 56*t^6 - 84*t^5 + 1470*t^4 - 5124*t^3 + 12824*t^2 - 14556*t - 7579,
    t^8 + 4*t^7 - 168*t^5 - 770*t^4 - 868*t^3 + 728*t^2 + 760*t - 6991,
    t^8 + 4*t^7 + 140*t^5 - 490*t^4 + 15036*t^3 + 7504*t^2 + 1220*t - 6915,
    t^8 + 4*t^7 + 140*t^5 - 616*t^3 + 336*t^2 + 1040*t - 6760,
    t^8 + 4*t^7 - 1330*t^4 + 7084*t^3 - 20104*t^2 + 15600*t - 6095,
    t^8 + 4*t^7 + 252*t^5 + 3220*t^4 + 15792*t^3 + 18928*t^2 + 6920*t - 5836,
    t^8 + 4*t^7 - 896*t^3 - 3584*t^2 - 5120*t - 2560,
    t^8 + 4*t^7 - 308*t^5 - 2030*t^4 - 6748*t^3 - 13272*t^2 - 8900*t - 2231,
    t^8 + 4*t^7 + 280*t^5 - 560*t^4 + 1624*t^3 - 2184*t^2 - 4000*t - 1580,
    t^8 + 4*t^7 - 56*t^6 - 504*t^5 - 1750*t^4 - 3052*t^3 - 2688*t^2 - 1208*t - 1367,
    t^8 + 4*t^7 - 56*t^6 - 84*t^5 + 840*t^4 - 2016*t^3 + 2016*t^2 + 176*t - 1256,
    t^8 + 4*t^7 - 56*t^6 + 140*t^5 - 140*t^4 - 112*t^3 + 112*t^2 + 152*t - 1100,
    t^8 + 4*t^7 - 28*t^6 - 168*t^5 - 140*t^4 + 560*t^3 + 840*t^2 - 480*t - 940,
    t^8 + 4*t^7 + 140*t^5 - 70*t^4 + 3724*t^3 - 11144*t^2 + 2180*t - 835,
    t^8 + 4*t^7 - 448*t^5 - 3640*t^4 - 13160*t^3 - 25480*t^2 - 22640*t - 540,
    t^8 + 4*t^7 - 56*t^6 - 280*t^5 + 672*t^3 + 448*t^2 - 192*t - 320,
    t^8 + 4*t^7 - 28*t^6 - 28*t^5 + 210*t^4 - 84*t^3 - 476*t^2 + 572*t - 183,
    t^8 + 4*t^7 - 56*t^6 - 84*t^5 + 490*t^4 + 924*t^3 + 336*t^2 + 116*t - 131,
    t^8 + 4*t^7 - 28*t^5 + 70*t^4 - 308*t^3 - 672*t^2 - 500*t - 131,
    t^8 + 4*t^7 - 28*t^5 - 70*t^4 + 812*t^3 - 952*t^2 + 620*t - 131,
    t^8 + 4*t^7 - 140*t^5 + 1820*t^4 + 4928*t^3 - 10528*t^2 + 2920*t - 220,
    t^8 + 4*t^7 - 56*t^6 - 504*t^5 - 1960*t^4 - 3024*t^3 + 2464*t^2 - 416*t + 16,
    t^8 + 4*t^7 - 56*t^6 - 140*t^5 + 1400*t^4 - 3360*t^3 + 3360*t^2 - 1200*t - 40,
    t^8 + 4*t^7 + 84*t^6 + 756*t^5 + 4270*t^4 + 9884*t^3 + 10276*t^2 + 4396*t + 329,
    t^8 + 4*t^7 + 140*t^4 + 784*t^3 + 896*t^2 + 480*t + 100,
    t^8 + 4*t^7 - 28*t^5 - 140*t^4 - 448*t^3 - 672*t^2 - 360*t + 324,
    t^8 + 4*t^7 - 70*t^4 + 84*t^3 + 56*t^2 - 80*t + 345,
    t^8 + 4*t^7 + 84*t^6 - 140*t^5 + 1260*t^4 - 6720*t^3 + 1960*t^2 - 9880*t + 660,
    t^8 + 4*t^7 - 280*t^5 + 280*t^4 + 5600*t^3 + 20720*t^2 + 12800*t + 1920,
    t^8 + 4*t^7 + 112*t^5 + 630*t^4 + 532*t^3 - 672*t^2 + 28200*t + 1969,
    t^8 + 4*t^7 + 112*t^5 + 70*t^4 - 868*t^3 + 3528*t^2 - 8480*t + 2809,
    t^8 + 4*t^7 - 56*t^6 - 280*t^5 + 350*t^4 + 5012*t^3 + 13048*t^2 + 13328*t + 3465,
    t^8 + 4*t^7 + 252*t^5 + 1610*t^4 - 1764*t^3 + 8344*t^2 + 14340*t + 4797,
    t^8 + 4*t^7 + 280*t^5 + 280*t^4 + 2800*t^2 - 1600*t + 4800,
    t^8 + 4*t^7 - 56*t^6 - 280*t^5 + 280*t^4 + 1792*t^3 - 112*t^2 - 9792*t + 6080,
    t^8 + 4*t^7 - 28*t^6 + 112*t^5 - 350*t^4 + 588*t^3 + 4452*t^2 + 24736*t + 7181,
    t^8 + 4*t^7 - 308*t^5 - 1190*t^4 - 1764*t^3 + 1624*t^2 + 6900*t + 9197,
    t^8 + 4*t^7 - 56*t^6 - 224*t^5 + 1190*t^4 + 9156*t^3 + 22344*t^2 + 23944*t + 9361,
    t^8 + 4*t^7 - 56*t^6 + 1330*t^4 + 1764*t^3 - 4144*t^2 - 7504*t + 13825,
    t^8 + 4*t^7 - 168*t^5 + 280*t^4 + 1232*t^3 - 1792*t^2 - 8480*t + 13904,
    t^8 + 4*t^7 - 56*t^6 - 84*t^5 + 770*t^4 + 924*t^3 - 1904*t^2 + 6356*t + 14469,
    t^8 + 4*t^7 - 140*t^5 - 560*t^4 - 56*t^3 + 5376*t^2 + 17840*t + 15640,
    t^8 + 4*t^7 - 56*t^6 - 364*t^5 + 420*t^4 + 2352*t^3 - 2352*t^2 - 1112*t + 16692,
    t^8 + 4*t^7 + 140*t^5 + 1050*t^4 + 1484*t^3 - 2184*t^2 + 3140*t + 19805,
    t^8 + 4*t^7 - 56*t^6 - 280*t^5 + 980*t^4 + 10640*t^3 + 36960*t^2 + 61520*t + 26420,
    t^8 - 28*t^6 - 112*t^5 + 210*t^4 + 2968*t^3 + 2660*t^2 - 12264*t - 81991,
    t^8 - 280*t^4 + 6720*t^2 - 70000,
    t^8 - 28*t^6 - 112*t^5 - 210*t^4 + 4256*t^3 + 4340*t^2 + 21072*t - 31367,
    t^8 + 28*t^6 - 196*t^5 - 70*t^4 + 5824*t^3 - 21980*t^2 + 35052*t - 19439,
    t^8 + 28*t^6 - 84*t^5 - 2688*t^3 + 9520*t^2 + 416*t - 19208,
    t^8 - 28*t^6 - 28*t^5 + 630*t^4 + 2352*t^3 + 140*t^2 - 11116*t - 16331,
    t^8 - 140*t^5 + 1610*t^4 - 8736*t^3 + 11480*t^2 + 9700*t - 18375,
    t^8 - 1400*t^4 + 21000*t^2 - 17500,
    t^8 - 28*t^6 - 112*t^5 + 350*t^4 + 2016*t^3 + 11620*t^2 + 432*t - 11767,
    t^8 + 28*t^6 - 84*t^5 + 490*t^4 + 168*t^3 - 4060*t^2 - 13636*t - 11907,
    t^8 + 28*t^6 - 196*t^5 + 630*t^4 - 2240*t^3 + 7700*t^2 - 16100*t - 3675,
    t^8 + 28*t^6 - 336*t^5 + 2730*t^4 - 7896*t^3 + 10780*t^2 + 19112*t - 2639,
    t^8 - 28*t^6 - 112*t^5 + 2240*t^4 + 2576*t^3 + 5040*t^2 + 30112*t - 2352,
    t^8 + 28*t^6 - 56*t^5 + 910*t^4 - 448*t^3 - 8260*t^2 - 8264*t - 2247,
    t^8 - 28*t^6 - 28*t^5 + 490*t^4 - 448*t^3 - 700*t^2 + 1484*t - 1771,
    t^8 - 28*t^6 - 168*t^5 + 770*t^4 + 1512*t^3 + 980*t^2 - 1456*t - 1351,
    t^8 - 28*t^6 - 112*t^5 + 2030*t^4 - 16352*t^3 - 4620*t^2 - 13104*t - 1351,
    t^8 - 840*t^4 - 2240*t^2 - 2800,
    t^8 - 28*t^6 - 168*t^5 - 490*t^4 - 784*t^3 - 700*t^2 - 8*t - 63,
    t^8 - 28*t^6 - 112*t^5 + 112*t^3 + 560*t^2 + 544*t + 336,
    t^8 - 28*t^6 - 28*t^5 + 280*t^4 + 616*t^3 + 72*t - 28,
    t^8 + 490*t^4 + 840*t^2 - 175,
    t^8 + 28*t^6 - 56*t^5 + 420*t^4 - 2072*t^3 - 280*t^2 + 5024*t + 2772,
    t^8 - 280*t^2 - 700,
    t^8 - 280*t^5 - 1540*t^4 - 3640*t^3 - 4480*t^2 - 2800*t - 700,
    t^8 - 28*t^6 - 112*t^5 + 350*t^4 + 3808*t^3 + 12180*t^2 + 35216*t + 5929,
    t^8 - 28*t^6 - 112*t^5 - 210*t^4 + 6608*t^3 + 140*t^2 + 336*t + 7189,
    t^8 - 28*t^6 - 308*t^5 - 1470*t^4 - 7448*t^3 + 23660*t^2 - 22596*t + 7189,
    t^8 - 280*t^5 + 1890*t^4 - 7168*t^3 + 14840*t^2 - 15720*t + 4725,
    t^8 + 672*t^3 + 840*t^2 + 1120*t + 4900,
    t^8 - 672*t^3 + 840*t^2 - 1120*t + 4900,
    t^8 + 28*t^6 - 84*t^5 - 560*t^4 - 840*t^3 + 5600*t^2 + 800*t + 12600,
    t^8 - 140*t^5 - 840*t^3 + 1680*t^2 - 2800*t + 7000,
    t^8 - 28*t^6 - 28*t^5 - 70*t^4 + 392*t^3 + 7980*t^2 + 21924*t + 15309,
    t^8 + 28*t^6 - 224*t^5 + 630*t^4 - 2464*t^3 + 11060*t^2 - 26032*t + 21021,
    t^8 + 28*t^6 - 196*t^5 - 420*t^4 - 5544*t^3 - 6440*t^2 - 22232*t + 27524,
    t^8 + 28*t^6 - 84*t^5 + 490*t^4 - 2016*t^3 - 7700*t^2 + 10372*t + 47509,
    t^8 - 28*t^6 - 112*t^5 + 630*t^4 + 1568*t^3 - 2940*t^2 - 24944*t + 49329,
    t^8 - 140*t^4 + 840*t^3 - 1120*t^2 + 22400*t + 91700,
    t^8 - 140*t^4 - 840*t^3 - 1120*t^2 - 22400*t + 91700,
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