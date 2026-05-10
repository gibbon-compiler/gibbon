open GibbonCompat;

datatype dat_ColorOctree = CNode of (int  * int * int * int * int * int * int * int * int * int * int * int * int * int *  dat_ColorOctree *  dat_ColorOctree *  dat_ColorOctree *  dat_ColorOctree *  dat_ColorOctree *  dat_ColorOctree *  dat_ColorOctree *  dat_ColorOctree) | CPixel of (int  * int * int)| CEmpty ;

fun internal_traverse_ColorOctree (arg_1002_1496_2205) = (case arg_1002_1496_2205 of CNode (x_1003_1497_2206 , x_1004_1498_2207, x_1005_1499_2208, x_1006_1500_2209, x_1007_1501_2210, x_1008_1502_2211, x_1009_1503_2212, x_1010_1504_2213, x_1011_1505_2214, x_1012_1506_2215, x_1013_1507_2216, x_1014_1508_2217, x_1015_1509_2218, x_1016_1510_2219, x_1017_1511_2220, x_1018_1512_2221, x_1019_1513_2222, x_1020_1514_2223, x_1021_1515_2224, x_1022_1516_2225, x_1023_1517_2226, x_1024_1518_2227) => 
  let val y_1039_1519_2228 = (internal_traverse_ColorOctree x_1017_1511_2220) in 
  let val y_1040_1520_2229 = (internal_traverse_ColorOctree x_1018_1512_2221) in 
  let val y_1041_1521_2230 = (internal_traverse_ColorOctree x_1019_1513_2222) in 
  let val y_1042_1522_2231 = (internal_traverse_ColorOctree x_1020_1514_2223) in 
  let val y_1043_1523_2232 = (internal_traverse_ColorOctree x_1021_1515_2224) in 
  let val y_1044_1524_2233 = (internal_traverse_ColorOctree x_1022_1516_2225) in 
  let val y_1045_1525_2234 = (internal_traverse_ColorOctree x_1023_1517_2226) in 
  let val y_1046_1526_2235 = (internal_traverse_ColorOctree x_1024_1518_2227) in () end end end end end end end end 
  | CPixel (x_1047_1527_2236 , x_1048_1528_2237, x_1049_1529_2238) => ()
  | CEmpty => ());

fun sum8 (a_503_1420_2005 , b_504_1421_2006, c_505_1422_2007, d_506_1423_2008, e_507_1424_2009, f_508_1425_2010, g_509_1426_2011, h_510_1427_2012) = 
  let val fltPrm_1568_2013 = (a_503_1420_2005 + b_504_1421_2006) in 
  let val fltPrm_1567_2014 = (fltPrm_1568_2013 + c_505_1422_2007) in 
  let val fltPrm_1566_2015 = (fltPrm_1567_2014 + d_506_1423_2008) in 
  let val fltPrm_1565_2016 = (fltPrm_1566_2015 + e_507_1424_2009) in 
  let val fltPrm_1564_2017 = (fltPrm_1565_2016 + f_508_1425_2010) in 
  let val fltPrm_1563_2018 = (fltPrm_1564_2017 + g_509_1426_2011) in (fltPrm_1563_2018 + h_510_1427_2012) end end end end end end;

fun cSumR (t_477_1394_1979) = (case t_477_1394_1979 of CNode (r_478_1395_1980 , wildcard__12_479_1396_1981, wildcard__13_480_1397_1982, wildcard__14_481_1398_1983, wildcard__15_482_1399_1984, wildcard__16_483_1400_1985, wildcard__17_484_1401_1986, wildcard__18_485_1402_1987, wildcard__19_486_1403_1988, wildcard__20_487_1404_1989, wildcard__21_488_1405_1990, wildcard__22_489_1406_1991, wildcard__23_490_1407_1992, wildcard__24_491_1408_1993, wildcard__25_492_1409_1994, wildcard__26_493_1410_1995, wildcard__27_494_1411_1996, wildcard__28_495_1412_1997, wildcard__29_496_1413_1998, wildcard__30_497_1414_1999, wildcard__31_498_1415_2000, wildcard__32_499_1416_2001) => r_478_1395_1980 
  | CPixel (r_500_1417_2002 , wildcard__55_501_1418_2003, wildcard__56_502_1419_2004) => r_500_1417_2002
  | CEmpty => 0);

fun absI (x_476_1393_1977) = 
  let val fltIf_1562_1978 = (x_476_1393_1977 < 0) in 
  (if fltIf_1562_1978 then (0 - x_476_1393_1977) 
   else x_476_1393_1977) end;

fun quantizationErrorProxy (t_511_1428_2019 , maxDepth_512_1429_2020, eta_513_1430_2021, weight_514_1431_2022) = (case t_511_1428_2019 of CNode (sr_515_1432_2023 , sg_516_1433_2024, sb_517_1434_2025, cnt_518_1435_2026, lvl_519_1436_2027, wildcard__283_520_1437_2028, wildcard__284_521_1438_2029, wildcard__285_522_1439_2030, wildcard__286_523_1440_2031, wildcard__287_524_1441_2032, wildcard__288_525_1442_2033, wildcard__289_526_1443_2034, wildcard__290_527_1444_2035, wildcard__291_528_1445_2036, a_529_1446_2037, b_530_1447_2038, c_531_1448_2039, d_532_1449_2040, e_533_1450_2041, f_534_1451_2042, g_535_1452_2043, h_536_1453_2044) => 
  let val depthTerm_537_1454_2045 = (lvl_519_1436_2027 + 1) in 
  let val farLhs_538_1455_2046 = (cnt_518_1435_2026 * 10) in 
  let val farRhs_539_1456_2047 = (eta_513_1430_2021 * depthTerm_537_1454_2045) in 
  let val fltIf_1569_2048 = (cnt_518_1435_2026 = 0) in 
  let val r_540_1457_2049 = 
  (if fltIf_1569_2048 then 0 
   else (sr_515_1432_2023 div cnt_518_1435_2026)) in 
  let val fltIf_1570_2050 = (cnt_518_1435_2026 = 0) in 
  let val g0_541_1458_2051 = 
  (if fltIf_1570_2050 then 0 
   else (sg_516_1433_2024 div cnt_518_1435_2026)) in 
  let val fltIf_1571_2052 = (cnt_518_1435_2026 = 0) in 
  let val b0_542_1459_2053 = 
  (if fltIf_1571_2052 then 0 
   else (sb_517_1434_2025 div cnt_518_1435_2026)) in 
  let val fltAppE_1575_2054 = (r_540_1457_2049 - g0_541_1458_2051) in 
  let val fltPrm_1574_2055 = (absI fltAppE_1575_2054) in 
  let val fltAppE_1577_2056 = (g0_541_1458_2051 - b0_542_1459_2053) in 
  let val fltPrm_1576_2057 = (absI fltAppE_1577_2056) in 
  let val fltPrm_1573_2058 = (fltPrm_1574_2055 + fltPrm_1576_2057) in 
  let val fltAppE_1579_2059 = (b0_542_1459_2053 - r_540_1457_2049) in 
  let val fltPrm_1578_2060 = (absI fltAppE_1579_2059) in 
  let val fltPrm_1572_2061 = (fltPrm_1573_2058 + fltPrm_1578_2060) in 
  let val approx_543_1460_2062 = (fltPrm_1572_2061 * weight_514_1431_2022) in 
  let val fltAppE_1580_2063 = (quantizationErrorProxy(a_529_1446_2037 , maxDepth_512_1429_2020, eta_513_1430_2021, weight_514_1431_2022)) in 
  let val fltAppE_1581_2064 = (quantizationErrorProxy(b_530_1447_2038 , maxDepth_512_1429_2020, eta_513_1430_2021, weight_514_1431_2022)) in 
  let val fltAppE_1582_2065 = (quantizationErrorProxy(c_531_1448_2039 , maxDepth_512_1429_2020, eta_513_1430_2021, weight_514_1431_2022)) in 
  let val fltAppE_1583_2066 = (quantizationErrorProxy(d_532_1449_2040 , maxDepth_512_1429_2020, eta_513_1430_2021, weight_514_1431_2022)) in 
  let val fltAppE_1584_2067 = (quantizationErrorProxy(e_533_1450_2041 , maxDepth_512_1429_2020, eta_513_1430_2021, weight_514_1431_2022)) in 
  let val fltAppE_1585_2068 = (quantizationErrorProxy(f_534_1451_2042 , maxDepth_512_1429_2020, eta_513_1430_2021, weight_514_1431_2022)) in 
  let val fltAppE_1586_2069 = (quantizationErrorProxy(g_535_1452_2043 , maxDepth_512_1429_2020, eta_513_1430_2021, weight_514_1431_2022)) in 
  let val fltAppE_1587_2070 = (quantizationErrorProxy(h_536_1453_2044 , maxDepth_512_1429_2020, eta_513_1430_2021, weight_514_1431_2022)) in 
  let val recur_544_1461_2071 = (sum8(fltAppE_1580_2063 , fltAppE_1581_2064, fltAppE_1582_2065, fltAppE_1583_2066, fltAppE_1584_2067, fltAppE_1585_2068, fltAppE_1586_2069, fltAppE_1587_2070)) in 
  let val fltPrm_1589_2072 = (lvl_519_1436_2027 >= maxDepth_512_1429_2020) in 
  let val fltPrm_1590_2073 = (farLhs_538_1455_2046 < farRhs_539_1456_2047) in 
  let val fltIf_1588_2074 = (fltPrm_1589_2072 orelse fltPrm_1590_2073) in 
  (if fltIf_1588_2074 then approx_543_1460_2062 
   else recur_544_1461_2071) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end 
  | CPixel (r_545_1462_2075 , g_546_1463_2076, b_547_1464_2077) => 
  let val fltAppE_1593_2078 = (r_545_1462_2075 - g_546_1463_2076) in 
  let val fltPrm_1592_2079 = (absI fltAppE_1593_2078) in 
  let val fltAppE_1595_2080 = (g_546_1463_2076 - b_547_1464_2077) in 
  let val fltPrm_1594_2081 = (absI fltAppE_1595_2080) in 
  let val fltPrm_1591_2082 = (fltPrm_1592_2079 + fltPrm_1594_2081) in 
  let val fltAppE_1597_2083 = (b_547_1464_2077 - r_545_1462_2075) in 
  let val fltPrm_1596_2084 = (absI fltAppE_1597_2083) in (fltPrm_1591_2082 + fltPrm_1596_2084) end end end end end end end
  | CEmpty => 0);

fun mixSeed (s_474_1391_1972 , salt_475_1392_1973) = 
  let val fltPrm_1560_1974 = (s_474_1391_1972 * 1103) in 
  let val fltPrm_1561_1975 = (salt_475_1392_1973 * 97) in 
  let val fltPrm_1559_1976 = (fltPrm_1560_1974 + fltPrm_1561_1975) in (fltPrm_1559_1976 + 13) end end end;

fun cCount (t_448_1365_1946) = (case t_448_1365_1946 of CNode (wildcard__159_449_1366_1947 , wildcard__160_450_1367_1948, wildcard__161_451_1368_1949, cnt_452_1369_1950, wildcard__162_453_1370_1951, wildcard__163_454_1371_1952, wildcard__164_455_1372_1953, wildcard__165_456_1373_1954, wildcard__166_457_1374_1955, wildcard__167_458_1375_1956, wildcard__168_459_1376_1957, wildcard__169_460_1377_1958, wildcard__170_461_1378_1959, wildcard__171_462_1379_1960, wildcard__172_463_1380_1961, wildcard__173_464_1381_1962, wildcard__174_465_1382_1963, wildcard__175_466_1383_1964, wildcard__176_467_1384_1965, wildcard__177_468_1385_1966, wildcard__178_469_1386_1967, wildcard__179_470_1387_1968) => cnt_452_1369_1950 
  | CPixel (wildcard__202_471_1388_1969 , wildcard__203_472_1389_1970, wildcard__204_473_1390_1971) => 1
  | CEmpty => 0);

fun cSumB (t_422_1339_1920) = (case t_422_1339_1920 of CNode (wildcard__110_423_1340_1921 , wildcard__111_424_1341_1922, b_425_1342_1923, wildcard__112_426_1343_1924, wildcard__113_427_1344_1925, wildcard__114_428_1345_1926, wildcard__115_429_1346_1927, wildcard__116_430_1347_1928, wildcard__117_431_1348_1929, wildcard__118_432_1349_1930, wildcard__119_433_1350_1931, wildcard__120_434_1351_1932, wildcard__121_435_1352_1933, wildcard__122_436_1353_1934, wildcard__123_437_1354_1935, wildcard__124_438_1355_1936, wildcard__125_439_1356_1937, wildcard__126_440_1357_1938, wildcard__127_441_1358_1939, wildcard__128_442_1359_1940, wildcard__129_443_1360_1941, wildcard__130_444_1361_1942) => b_425_1342_1923 
  | CPixel (wildcard__153_445_1362_1943 , wildcard__154_446_1363_1944, b_447_1364_1945) => b_447_1364_1945
  | CEmpty => 0);

fun internal_print_ColorOctree (arg_1053_1257_1838) = (case arg_1053_1257_1838 of CNode (x_1054_1258_1839 , x_1055_1259_1840, x_1056_1260_1841, x_1057_1261_1842, x_1058_1262_1843, x_1059_1263_1844, x_1060_1264_1845, x_1061_1265_1846, x_1062_1266_1847, x_1063_1267_1848, x_1064_1268_1849, x_1065_1269_1850, x_1066_1270_1851, x_1067_1271_1852, x_1068_1272_1853, x_1069_1273_1854, x_1070_1274_1855, x_1071_1275_1856, x_1072_1276_1857, x_1073_1277_1858, x_1074_1278_1859, x_1075_1279_1860) => 
  let val wildcard_1098_1280_1861 = (print "(CNode") in 
  let val wildcard_1121_1281_1862 = (print " ") in 
  let val y_1076_1282_1863 = (print(Int.toString(x_1054_1258_1839))) in 
  let val wildcard_1120_1283_1864 = (print " ") in 
  let val y_1077_1284_1865 = (print(Int.toString(x_1055_1259_1840))) in 
  let val wildcard_1119_1285_1866 = (print " ") in 
  let val y_1078_1286_1867 = (print(Int.toString(x_1056_1260_1841))) in 
  let val wildcard_1118_1287_1868 = (print " ") in 
  let val y_1079_1288_1869 = (print(Int.toString(x_1057_1261_1842))) in 
  let val wildcard_1117_1289_1870 = (print " ") in 
  let val y_1080_1290_1871 = (print(Int.toString(x_1058_1262_1843))) in 
  let val wildcard_1116_1291_1872 = (print " ") in 
  let val y_1081_1292_1873 = (print(Int.toString(x_1059_1263_1844))) in 
  let val wildcard_1115_1293_1874 = (print " ") in 
  let val y_1082_1294_1875 = (print(Int.toString(x_1060_1264_1845))) in 
  let val wildcard_1114_1295_1876 = (print " ") in 
  let val y_1083_1296_1877 = (print(Int.toString(x_1061_1265_1846))) in 
  let val wildcard_1113_1297_1878 = (print " ") in 
  let val y_1084_1298_1879 = (print(Int.toString(x_1062_1266_1847))) in 
  let val wildcard_1112_1299_1880 = (print " ") in 
  let val y_1085_1300_1881 = (print(Int.toString(x_1063_1267_1848))) in 
  let val wildcard_1111_1301_1882 = (print " ") in 
  let val y_1086_1302_1883 = (print(Int.toString(x_1064_1268_1849))) in 
  let val wildcard_1110_1303_1884 = (print " ") in 
  let val y_1087_1304_1885 = (print(Int.toString(x_1065_1269_1850))) in 
  let val wildcard_1109_1305_1886 = (print " ") in 
  let val y_1088_1306_1887 = (print(Int.toString(x_1066_1270_1851))) in 
  let val wildcard_1108_1307_1888 = (print " ") in 
  let val y_1089_1308_1889 = (print(Int.toString(x_1067_1271_1852))) in 
  let val wildcard_1107_1309_1890 = (print " ") in 
  let val y_1090_1310_1891 = (internal_print_ColorOctree x_1068_1272_1853) in 
  let val wildcard_1106_1311_1892 = (print " ") in 
  let val y_1091_1312_1893 = (internal_print_ColorOctree x_1069_1273_1854) in 
  let val wildcard_1105_1313_1894 = (print " ") in 
  let val y_1092_1314_1895 = (internal_print_ColorOctree x_1070_1274_1855) in 
  let val wildcard_1104_1315_1896 = (print " ") in 
  let val y_1093_1316_1897 = (internal_print_ColorOctree x_1071_1275_1856) in 
  let val wildcard_1103_1317_1898 = (print " ") in 
  let val y_1094_1318_1899 = (internal_print_ColorOctree x_1072_1276_1857) in 
  let val wildcard_1102_1319_1900 = (print " ") in 
  let val y_1095_1320_1901 = (internal_print_ColorOctree x_1073_1277_1858) in 
  let val wildcard_1101_1321_1902 = (print " ") in 
  let val y_1096_1322_1903 = (internal_print_ColorOctree x_1074_1278_1859) in 
  let val wildcard_1100_1323_1904 = (print " ") in 
  let val y_1097_1324_1905 = (internal_print_ColorOctree x_1075_1279_1860) in 
  let val wildcard_1099_1325_1906 = (print ")") in () end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end 
  | CPixel (x_1122_1326_1907 , x_1123_1327_1908, x_1124_1328_1909) => 
  let val wildcard_1128_1329_1910 = (print "(CPixel") in 
  let val wildcard_1132_1330_1911 = (print " ") in 
  let val y_1125_1331_1912 = (print(Int.toString(x_1122_1326_1907))) in 
  let val wildcard_1131_1332_1913 = (print " ") in 
  let val y_1126_1333_1914 = (print(Int.toString(x_1123_1327_1908))) in 
  let val wildcard_1130_1334_1915 = (print " ") in 
  let val y_1127_1335_1916 = (print(Int.toString(x_1124_1328_1909))) in 
  let val wildcard_1129_1336_1917 = (print ")") in () end end end end end end end end
  | CEmpty => 
  let val wildcard_1133_1337_1918 = (print "(CEmpty") in 
  let val wildcard_1134_1338_1919 = (print ")") in () end end);

fun paletteEntriesQuantized (t_390_1225_1779 , maxDepth_391_1226_1780, theta_392_1227_1781) = (case t_390_1225_1779 of CNode (wildcard__244_393_1228_1782 , wildcard__245_394_1229_1783, wildcard__246_395_1230_1784, cnt_396_1231_1785, lvl_397_1232_1786, minR_398_1233_1787, minG_399_1234_1788, minB_400_1235_1789, maxR_401_1236_1790, maxG_402_1237_1791, maxB_403_1238_1792, varP_404_1239_1793, energy_405_1240_1794, flags_406_1241_1795, a_407_1242_1796, b_408_1243_1797, c_409_1244_1798, d_410_1245_1799, e_411_1246_1800, f_412_1247_1801, g_413_1248_1802, h_414_1249_1803) => 
  let val fltAppE_1535_1804 = (maxR_401_1236_1790 - minR_398_1233_1787) in 
  let val fltPrm_1534_1805 = (absI fltAppE_1535_1804) in 
  let val fltAppE_1537_1806 = (maxG_402_1237_1791 - minG_399_1234_1788) in 
  let val fltPrm_1536_1807 = (absI fltAppE_1537_1806) in 
  let val fltPrm_1533_1808 = (fltPrm_1534_1805 + fltPrm_1536_1807) in 
  let val fltAppE_1539_1809 = (maxB_403_1238_1792 - minB_400_1235_1789) in 
  let val fltPrm_1538_1810 = (absI fltAppE_1539_1809) in 
  let val fltPrm_1532_1811 = (fltPrm_1533_1808 + fltPrm_1538_1810) in 
  let val fltPrm_1540_1812 = (varP_404_1239_1793 div 4) in 
  let val compact_415_1250_1813 = (fltPrm_1532_1811 + fltPrm_1540_1812) in 
  let val fltPrm_1542_1814 = (lvl_397_1232_1786 + 1) in 
  let val fltPrm_1541_1815 = (theta_392_1227_1781 * fltPrm_1542_1814) in 
  let val fltPrm_1543_1816 = (flags_406_1241_1795 * 2) in 
  let val threshold_416_1251_1817 = (fltPrm_1541_1815 + fltPrm_1543_1816) in 
  let val fltPrm_1545_1818 = (lvl_397_1232_1786 >= maxDepth_391_1226_1780) in 
  let val fltPrm_1546_1819 = (energy_405_1240_1794 < 12) in 
  let val fltIf_1544_1820 = (fltPrm_1545_1818 orelse fltPrm_1546_1819) in 
  let val approx_417_1252_1821 = 
  (if fltIf_1544_1820 then 1 
   else 0) in 
  let val fltAppE_1547_1822 = (paletteEntriesQuantized(a_407_1242_1796 , maxDepth_391_1226_1780, theta_392_1227_1781)) in 
  let val fltAppE_1548_1823 = (paletteEntriesQuantized(b_408_1243_1797 , maxDepth_391_1226_1780, theta_392_1227_1781)) in 
  let val fltAppE_1549_1824 = (paletteEntriesQuantized(c_409_1244_1798 , maxDepth_391_1226_1780, theta_392_1227_1781)) in 
  let val fltAppE_1550_1825 = (paletteEntriesQuantized(d_410_1245_1799 , maxDepth_391_1226_1780, theta_392_1227_1781)) in 
  let val fltAppE_1551_1826 = (paletteEntriesQuantized(e_411_1246_1800 , maxDepth_391_1226_1780, theta_392_1227_1781)) in 
  let val fltAppE_1552_1827 = (paletteEntriesQuantized(f_412_1247_1801 , maxDepth_391_1226_1780, theta_392_1227_1781)) in 
  let val fltAppE_1553_1828 = (paletteEntriesQuantized(g_413_1248_1802 , maxDepth_391_1226_1780, theta_392_1227_1781)) in 
  let val fltAppE_1554_1829 = (paletteEntriesQuantized(h_414_1249_1803 , maxDepth_391_1226_1780, theta_392_1227_1781)) in 
  let val recur_418_1253_1830 = (sum8(fltAppE_1547_1822 , fltAppE_1548_1823, fltAppE_1549_1824, fltAppE_1550_1825, fltAppE_1551_1826, fltAppE_1552_1827, fltAppE_1553_1828, fltAppE_1554_1829)) in 
  let val fltPrm_1558_1831 = (cnt_396_1231_1785 div 16) in 
  let val fltPrm_1557_1832 = (1 + fltPrm_1558_1831) in 
  let val fltPrm_1556_1833 = (compact_415_1250_1813 * fltPrm_1557_1832) in 
  let val fltIf_1555_1834 = (fltPrm_1556_1833 < threshold_416_1251_1817) in 
  (if fltIf_1555_1834 then (1 + approx_417_1252_1821) 
   else recur_418_1253_1830) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end 
  | CPixel (wildcard__273_419_1254_1835 , wildcard__274_420_1255_1836, wildcard__275_421_1256_1837) => 1
  | CEmpty => 0);

fun cSumG (t_364_1199_1753) = (case t_364_1199_1753 of CNode (wildcard__61_365_1200_1754 , g_366_1201_1755, wildcard__62_367_1202_1756, wildcard__63_368_1203_1757, wildcard__64_369_1204_1758, wildcard__65_370_1205_1759, wildcard__66_371_1206_1760, wildcard__67_372_1207_1761, wildcard__68_373_1208_1762, wildcard__69_374_1209_1763, wildcard__70_375_1210_1764, wildcard__71_376_1211_1765, wildcard__72_377_1212_1766, wildcard__73_378_1213_1767, wildcard__74_379_1214_1768, wildcard__75_380_1215_1769, wildcard__76_381_1216_1770, wildcard__77_382_1217_1771, wildcard__78_383_1218_1772, wildcard__79_384_1219_1773, wildcard__80_385_1220_1774, wildcard__81_386_1221_1775) => g_366_1201_1755 
  | CPixel (wildcard__104_387_1222_1776 , g_388_1223_1777, wildcard__105_389_1224_1778) => g_388_1223_1777
  | CEmpty => 0);

fun buildColorOctree (depth_548_1465_2085 , level_549_1466_2086, seed_550_1467_2087) = 
  let val fltIf_1598_2088 = (depth_548_1465_2085 = 0) in 
  (if fltIf_1598_2088 then 
  let val fltAppE_1600_2089 = (mixSeed(seed_550_1467_2087 , 3)) in 
  let val fltPrm_1599_2090 = (absI fltAppE_1600_2089) in 
  let val r_551_1468_2091 = (fltPrm_1599_2090 mod 256) in 
  let val fltAppE_1602_2092 = (mixSeed(seed_550_1467_2087 , 5)) in 
  let val fltPrm_1601_2093 = (absI fltAppE_1602_2092) in 
  let val g_552_1469_2094 = (fltPrm_1601_2093 mod 256) in 
  let val fltAppE_1604_2095 = (mixSeed(seed_550_1467_2087 , 7)) in 
  let val fltPrm_1603_2096 = (absI fltAppE_1604_2095) in 
  let val b_553_1470_2097 = (fltPrm_1603_2096 mod 256) in (CPixel (r_551_1468_2091 , g_552_1469_2094, b_553_1470_2097)) end end end end end end end end end 
   else 
  let val fltAppE_1605_2098 = (depth_548_1465_2085 - 1) in 
  let val fltAppE_1606_2099 = (level_549_1466_2086 + 1) in 
  let val fltAppE_1607_2100 = (mixSeed(seed_550_1467_2087 , 1)) in 
  let val c0_554_1471_2101 = (buildColorOctree(fltAppE_1605_2098 , fltAppE_1606_2099, fltAppE_1607_2100)) in 
  let val fltAppE_1608_2102 = (depth_548_1465_2085 - 1) in 
  let val fltAppE_1609_2103 = (level_549_1466_2086 + 1) in 
  let val fltAppE_1610_2104 = (mixSeed(seed_550_1467_2087 , 2)) in 
  let val c1_555_1472_2105 = (buildColorOctree(fltAppE_1608_2102 , fltAppE_1609_2103, fltAppE_1610_2104)) in 
  let val fltAppE_1611_2106 = (depth_548_1465_2085 - 1) in 
  let val fltAppE_1612_2107 = (level_549_1466_2086 + 1) in 
  let val fltAppE_1613_2108 = (mixSeed(seed_550_1467_2087 , 3)) in 
  let val c2_556_1473_2109 = (buildColorOctree(fltAppE_1611_2106 , fltAppE_1612_2107, fltAppE_1613_2108)) in 
  let val fltAppE_1614_2110 = (depth_548_1465_2085 - 1) in 
  let val fltAppE_1615_2111 = (level_549_1466_2086 + 1) in 
  let val fltAppE_1616_2112 = (mixSeed(seed_550_1467_2087 , 4)) in 
  let val c3_557_1474_2113 = (buildColorOctree(fltAppE_1614_2110 , fltAppE_1615_2111, fltAppE_1616_2112)) in 
  let val fltAppE_1617_2114 = (depth_548_1465_2085 - 1) in 
  let val fltAppE_1618_2115 = (level_549_1466_2086 + 1) in 
  let val fltAppE_1619_2116 = (mixSeed(seed_550_1467_2087 , 5)) in 
  let val c4_558_1475_2117 = (buildColorOctree(fltAppE_1617_2114 , fltAppE_1618_2115, fltAppE_1619_2116)) in 
  let val fltAppE_1620_2118 = (depth_548_1465_2085 - 1) in 
  let val fltAppE_1621_2119 = (level_549_1466_2086 + 1) in 
  let val fltAppE_1622_2120 = (mixSeed(seed_550_1467_2087 , 6)) in 
  let val c5_559_1476_2121 = (buildColorOctree(fltAppE_1620_2118 , fltAppE_1621_2119, fltAppE_1622_2120)) in 
  let val fltAppE_1623_2122 = (depth_548_1465_2085 - 1) in 
  let val fltAppE_1624_2123 = (level_549_1466_2086 + 1) in 
  let val fltAppE_1625_2124 = (mixSeed(seed_550_1467_2087 , 7)) in 
  let val c6_560_1477_2125 = (buildColorOctree(fltAppE_1623_2122 , fltAppE_1624_2123, fltAppE_1625_2124)) in 
  let val fltAppE_1626_2126 = (depth_548_1465_2085 - 1) in 
  let val fltAppE_1627_2127 = (level_549_1466_2086 + 1) in 
  let val fltAppE_1628_2128 = (mixSeed(seed_550_1467_2087 , 8)) in 
  let val c7_561_1478_2129 = (buildColorOctree(fltAppE_1626_2126 , fltAppE_1627_2127, fltAppE_1628_2128)) in 
  let val fltAppE_1629_2130 = (cSumR c0_554_1471_2101) in 
  let val fltAppE_1630_2131 = (cSumR c1_555_1472_2105) in 
  let val fltAppE_1631_2132 = (cSumR c2_556_1473_2109) in 
  let val fltAppE_1632_2133 = (cSumR c3_557_1474_2113) in 
  let val fltAppE_1633_2134 = (cSumR c4_558_1475_2117) in 
  let val fltAppE_1634_2135 = (cSumR c5_559_1476_2121) in 
  let val fltAppE_1635_2136 = (cSumR c6_560_1477_2125) in 
  let val fltAppE_1636_2137 = (cSumR c7_561_1478_2129) in 
  let val sr_562_1479_2138 = (sum8(fltAppE_1629_2130 , fltAppE_1630_2131, fltAppE_1631_2132, fltAppE_1632_2133, fltAppE_1633_2134, fltAppE_1634_2135, fltAppE_1635_2136, fltAppE_1636_2137)) in 
  let val fltAppE_1637_2139 = (cSumG c0_554_1471_2101) in 
  let val fltAppE_1638_2140 = (cSumG c1_555_1472_2105) in 
  let val fltAppE_1639_2141 = (cSumG c2_556_1473_2109) in 
  let val fltAppE_1640_2142 = (cSumG c3_557_1474_2113) in 
  let val fltAppE_1641_2143 = (cSumG c4_558_1475_2117) in 
  let val fltAppE_1642_2144 = (cSumG c5_559_1476_2121) in 
  let val fltAppE_1643_2145 = (cSumG c6_560_1477_2125) in 
  let val fltAppE_1644_2146 = (cSumG c7_561_1478_2129) in 
  let val sg_563_1480_2147 = (sum8(fltAppE_1637_2139 , fltAppE_1638_2140, fltAppE_1639_2141, fltAppE_1640_2142, fltAppE_1641_2143, fltAppE_1642_2144, fltAppE_1643_2145, fltAppE_1644_2146)) in 
  let val fltAppE_1645_2148 = (cSumB c0_554_1471_2101) in 
  let val fltAppE_1646_2149 = (cSumB c1_555_1472_2105) in 
  let val fltAppE_1647_2150 = (cSumB c2_556_1473_2109) in 
  let val fltAppE_1648_2151 = (cSumB c3_557_1474_2113) in 
  let val fltAppE_1649_2152 = (cSumB c4_558_1475_2117) in 
  let val fltAppE_1650_2153 = (cSumB c5_559_1476_2121) in 
  let val fltAppE_1651_2154 = (cSumB c6_560_1477_2125) in 
  let val fltAppE_1652_2155 = (cSumB c7_561_1478_2129) in 
  let val sb_564_1481_2156 = (sum8(fltAppE_1645_2148 , fltAppE_1646_2149, fltAppE_1647_2150, fltAppE_1648_2151, fltAppE_1649_2152, fltAppE_1650_2153, fltAppE_1651_2154, fltAppE_1652_2155)) in 
  let val fltAppE_1653_2157 = (cCount c0_554_1471_2101) in 
  let val fltAppE_1654_2158 = (cCount c1_555_1472_2105) in 
  let val fltAppE_1655_2159 = (cCount c2_556_1473_2109) in 
  let val fltAppE_1656_2160 = (cCount c3_557_1474_2113) in 
  let val fltAppE_1657_2161 = (cCount c4_558_1475_2117) in 
  let val fltAppE_1658_2162 = (cCount c5_559_1476_2121) in 
  let val fltAppE_1659_2163 = (cCount c6_560_1477_2125) in 
  let val fltAppE_1660_2164 = (cCount c7_561_1478_2129) in 
  let val cnt_565_1482_2165 = (sum8(fltAppE_1653_2157 , fltAppE_1654_2158, fltAppE_1655_2159, fltAppE_1656_2160, fltAppE_1657_2161, fltAppE_1658_2162, fltAppE_1659_2163, fltAppE_1660_2164)) in 
  let val fltIf_1661_2166 = (cnt_565_1482_2165 = 0) in 
  let val rMean_566_1483_2167 = 
  (if fltIf_1661_2166 then 0 
   else (sr_562_1479_2138 div cnt_565_1482_2165)) in 
  let val fltIf_1662_2168 = (cnt_565_1482_2165 = 0) in 
  let val gMean_567_1484_2169 = 
  (if fltIf_1662_2168 then 0 
   else (sg_563_1480_2147 div cnt_565_1482_2165)) in 
  let val fltIf_1663_2170 = (cnt_565_1482_2165 = 0) in 
  let val bMean_568_1485_2171 = 
  (if fltIf_1663_2170 then 0 
   else (sb_564_1481_2156 div cnt_565_1482_2165)) in 
  let val fltIf_1664_2172 = (rMean_566_1483_2167 > 20) in 
  let val minR_569_1486_2173 = 
  (if fltIf_1664_2172 then (rMean_566_1483_2167 - 20) 
   else 0) in 
  let val fltIf_1665_2174 = (gMean_567_1484_2169 > 20) in 
  let val minG_570_1487_2175 = 
  (if fltIf_1665_2174 then (gMean_567_1484_2169 - 20) 
   else 0) in 
  let val fltIf_1666_2176 = (bMean_568_1485_2171 > 20) in 
  let val minB_571_1488_2177 = 
  (if fltIf_1666_2176 then (bMean_568_1485_2171 - 20) 
   else 0) in 
  let val fltPrm_1668_2178 = (rMean_566_1483_2167 + 20) in 
  let val fltIf_1667_2179 = (fltPrm_1668_2178 < 255) in 
  let val maxR_572_1489_2180 = 
  (if fltIf_1667_2179 then (rMean_566_1483_2167 + 20) 
   else 255) in 
  let val fltPrm_1670_2181 = (gMean_567_1484_2169 + 20) in 
  let val fltIf_1669_2182 = (fltPrm_1670_2181 < 255) in 
  let val maxG_573_1490_2183 = 
  (if fltIf_1669_2182 then (gMean_567_1484_2169 + 20) 
   else 255) in 
  let val fltPrm_1672_2184 = (bMean_568_1485_2171 + 20) in 
  let val fltIf_1671_2185 = (fltPrm_1672_2184 < 255) in 
  let val maxB_574_1491_2186 = 
  (if fltIf_1671_2185 then (bMean_568_1485_2171 + 20) 
   else 255) in 
  let val fltAppE_1675_2187 = (maxR_572_1489_2180 - minR_569_1486_2173) in 
  let val fltPrm_1674_2188 = (absI fltAppE_1675_2187) in 
  let val fltAppE_1677_2189 = (maxG_573_1490_2183 - minG_570_1487_2175) in 
  let val fltPrm_1676_2190 = (absI fltAppE_1677_2189) in 
  let val fltPrm_1673_2191 = (fltPrm_1674_2188 + fltPrm_1676_2190) in 
  let val fltAppE_1679_2192 = (maxB_574_1491_2186 - minB_571_1488_2177) in 
  let val fltPrm_1678_2193 = (absI fltAppE_1679_2192) in 
  let val spread_575_1492_2194 = (fltPrm_1673_2191 + fltPrm_1678_2193) in 
  let val fltPrm_1681_2195 = (level_549_1466_2086 mod 3) in 
  let val fltPrm_1680_2196 = (1 + fltPrm_1681_2195) in 
  let val varP_576_1493_2197 = (spread_575_1492_2194 * fltPrm_1680_2196) in 
  let val fltPrm_1683_2198 = (sr_562_1479_2138 + sg_563_1480_2147) in 
  let val fltPrm_1682_2199 = (fltPrm_1683_2198 + sb_564_1481_2156) in 
  let val fltPrm_1684_2200 = (1 + cnt_565_1482_2165) in 
  let val energy_577_1494_2201 = (fltPrm_1682_2199 div fltPrm_1684_2200) in 
  let val fltAppE_1686_2202 = (mixSeed(seed_550_1467_2087 , 29)) in 
  let val fltPrm_1685_2203 = (absI fltAppE_1686_2202) in 
  let val flags_578_1495_2204 = (fltPrm_1685_2203 mod 8) in (CNode (sr_562_1479_2138 , sg_563_1480_2147, sb_564_1481_2156, cnt_565_1482_2165, level_549_1466_2086, minR_569_1486_2173, minG_570_1487_2175, minB_571_1488_2177, maxR_572_1489_2180, maxG_573_1490_2183, maxB_574_1491_2186, varP_576_1493_2197, energy_577_1494_2201, flags_578_1495_2204, c0_554_1471_2101, c1_555_1472_2105, c2_556_1473_2109, c3_557_1474_2113, c4_558_1475_2117, c5_559_1476_2121, c6_560_1477_2125, c7_561_1478_2129)) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end) end;

fun internal_copy_ColorOctree (arg_951_1148_1702) = (case arg_951_1148_1702 of CNode (x_952_1149_1703 , x_953_1150_1704, x_954_1151_1705, x_955_1152_1706, x_956_1153_1707, x_957_1154_1708, x_958_1155_1709, x_959_1156_1710, x_960_1157_1711, x_961_1158_1712, x_962_1159_1713, x_963_1160_1714, x_964_1161_1715, x_965_1162_1716, x_966_1163_1717, x_967_1164_1718, x_968_1165_1719, x_969_1166_1720, x_970_1167_1721, x_971_1168_1722, x_972_1169_1723, x_973_1170_1724) => 
  let val y_988_1185_1739 = (internal_copy_ColorOctree x_966_1163_1717) in 
  let val y_989_1186_1740 = (internal_copy_ColorOctree x_967_1164_1718) in 
  let val y_990_1187_1741 = (internal_copy_ColorOctree x_968_1165_1719) in 
  let val y_991_1188_1742 = (internal_copy_ColorOctree x_969_1166_1720) in 
  let val y_992_1189_1743 = (internal_copy_ColorOctree x_970_1167_1721) in 
  let val y_993_1190_1744 = (internal_copy_ColorOctree x_971_1168_1722) in 
  let val y_994_1191_1745 = (internal_copy_ColorOctree x_972_1169_1723) in 
  let val y_995_1192_1746 = (internal_copy_ColorOctree x_973_1170_1724) in (CNode (x_952_1149_1703 , x_953_1150_1704, x_954_1151_1705, x_955_1152_1706, x_956_1153_1707, x_957_1154_1708, x_958_1155_1709, x_959_1156_1710, x_960_1157_1711, x_961_1158_1712, x_962_1159_1713, x_963_1160_1714, x_964_1161_1715, x_965_1162_1716, y_988_1185_1739, y_989_1186_1740, y_990_1187_1741, y_991_1188_1742, y_992_1189_1743, y_993_1190_1744, y_994_1191_1745, y_995_1192_1746)) end end end end end end end end 
  | CPixel (x_996_1193_1747 , x_997_1194_1748, x_998_1195_1749) => (CPixel (x_996_1193_1747 , x_997_1194_1748, x_998_1195_1749))
  | CEmpty => CEmpty);
val _ = (case 
  let val wildcard__348_351_1135_1687 = (printsym "Running program ColorOctree Quantization: ") in 
  let val wildcard__346_352_1136_1688 = (printsym "NEWLINE") in 
  let val fltPrm_1531_1689 = (GibbonCompat.getSizeParam()) in 
  let val fltAppE_1530_1690 = (fltPrm_1531_1689 + 8) in 
  let val colorTree_353_1137_1691 = (buildColorOctree(fltAppE_1530_1690 , 0, 31)) in 
  let val wildcard__343_354_1138_1692 = (printsym "Running pass paletteEntriesQuantized (fold, uses=13): ") in 
  let val wildcard__341_355_1139_1693 = (printsym "NEWLINE") in 
  let val paletteEntries_356_1140_1694 = (iterate (fn () => paletteEntriesQuantized(colorTree_353_1137_1691 , 4, 12))) in 
  let val wildcard__337_357_1141_1695 = (printsym "End") in 
  let val wildcard__335_358_1142_1696 = (printsym "NEWLINE") in 
  let val wildcard__333_359_1143_1697 = (printsym "Running pass quantizationErrorProxy (fold, uses=10): ") in 
  let val wildcard__331_360_1144_1698 = (printsym "NEWLINE") in 
  let val quantError_361_1145_1699 = (iterate (fn () => quantizationErrorProxy(colorTree_353_1137_1691 , 4, 11, 3))) in 
  let val wildcard__327_362_1146_1700 = (printsym "End") in 
  let val wildcard__325_363_1147_1701 = (printsym "NEWLINE") in (paletteEntries_356_1140_1694 , quantError_361_1145_1699) end end end end end end end end end end end end end end end of (x__1 , x__2) => let val _ = print "#(" val _ = (print(Int.toString(x__1))) val _ = print " "val _ = (print(Int.toString(x__2))) val _ = print ")" in () end);
val _ = print "\n"
