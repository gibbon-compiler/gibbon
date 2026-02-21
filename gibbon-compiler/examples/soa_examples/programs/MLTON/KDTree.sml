open GibbonCompat;

datatype dat_KDTree = KDNode of (int  * int * int * int * int * int * int * int * int * int *  dat_KDTree *  dat_KDTree) | KDLeaf of (int  * int * int * int * int)| KDEmpty ;

fun internal_copy_KDTree (arg_893_1397_2084) = (case arg_893_1397_2084 of KDNode (x_894_1398_2085 , x_895_1399_2086, x_896_1400_2087, x_897_1401_2088, x_898_1402_2089, x_899_1403_2090, x_900_1404_2091, x_901_1405_2092, x_902_1406_2093, x_903_1407_2094, x_904_1408_2095, x_905_1409_2096) => 
  let val y_916_1420_2107 = (internal_copy_KDTree x_904_1408_2095) in 
  let val y_917_1421_2108 = (internal_copy_KDTree x_905_1409_2096) in (KDNode (x_894_1398_2085 , x_895_1399_2086, x_896_1400_2087, x_897_1401_2088, x_898_1402_2089, x_899_1403_2090, x_900_1404_2091, x_901_1405_2092, x_902_1406_2093, x_903_1407_2094, y_916_1420_2107, y_917_1421_2108)) end end 
  | KDLeaf (x_918_1422_2109 , x_919_1423_2110, x_920_1424_2111, x_921_1425_2112, x_922_1426_2113) => (KDLeaf (x_918_1422_2109 , x_919_1423_2110, x_920_1424_2111, x_921_1425_2112, x_922_1426_2113))
  | KDEmpty => KDEmpty);

fun internal_print_KDTree (arg_963_1339_2026) = (case arg_963_1339_2026 of KDNode (x_964_1340_2027 , x_965_1341_2028, x_966_1342_2029, x_967_1343_2030, x_968_1344_2031, x_969_1345_2032, x_970_1346_2033, x_971_1347_2034, x_972_1348_2035, x_973_1349_2036, x_974_1350_2037, x_975_1351_2038) => 
  let val wildcard_988_1352_2039 = (print "(KDNode") in 
  let val wildcard_1001_1353_2040 = (print " ") in 
  let val y_976_1354_2041 = (print(Int.toString(x_964_1340_2027))) in 
  let val wildcard_1000_1355_2042 = (print " ") in 
  let val y_977_1356_2043 = (print(Int.toString(x_965_1341_2028))) in 
  let val wildcard_999_1357_2044 = (print " ") in 
  let val y_978_1358_2045 = (print(Int.toString(x_966_1342_2029))) in 
  let val wildcard_998_1359_2046 = (print " ") in 
  let val y_979_1360_2047 = (print(Int.toString(x_967_1343_2030))) in 
  let val wildcard_997_1361_2048 = (print " ") in 
  let val y_980_1362_2049 = (print(Int.toString(x_968_1344_2031))) in 
  let val wildcard_996_1363_2050 = (print " ") in 
  let val y_981_1364_2051 = (print(Int.toString(x_969_1345_2032))) in 
  let val wildcard_995_1365_2052 = (print " ") in 
  let val y_982_1366_2053 = (print(Int.toString(x_970_1346_2033))) in 
  let val wildcard_994_1367_2054 = (print " ") in 
  let val y_983_1368_2055 = (print(Int.toString(x_971_1347_2034))) in 
  let val wildcard_993_1369_2056 = (print " ") in 
  let val y_984_1370_2057 = (print(Int.toString(x_972_1348_2035))) in 
  let val wildcard_992_1371_2058 = (print " ") in 
  let val y_985_1372_2059 = (print(Int.toString(x_973_1349_2036))) in 
  let val wildcard_991_1373_2060 = (print " ") in 
  let val y_986_1374_2061 = (internal_print_KDTree x_974_1350_2037) in 
  let val wildcard_990_1375_2062 = (print " ") in 
  let val y_987_1376_2063 = (internal_print_KDTree x_975_1351_2038) in 
  let val wildcard_989_1377_2064 = (print ")") in () end end end end end end end end end end end end end end end end end end end end end end end end end end 
  | KDLeaf (x_1002_1378_2065 , x_1003_1379_2066, x_1004_1380_2067, x_1005_1381_2068, x_1006_1382_2069) => 
  let val wildcard_1012_1383_2070 = (print "(KDLeaf") in 
  let val wildcard_1018_1384_2071 = (print " ") in 
  let val y_1007_1385_2072 = (print(Int.toString(x_1002_1378_2065))) in 
  let val wildcard_1017_1386_2073 = (print " ") in 
  let val y_1008_1387_2074 = (print(Int.toString(x_1003_1379_2066))) in 
  let val wildcard_1016_1388_2075 = (print " ") in 
  let val y_1009_1389_2076 = (print(Int.toString(x_1004_1380_2067))) in 
  let val wildcard_1015_1390_2077 = (print " ") in 
  let val y_1010_1391_2078 = (print(Int.toString(x_1005_1381_2068))) in 
  let val wildcard_1014_1392_2079 = (print " ") in 
  let val y_1011_1393_2080 = (print(Int.toString(x_1006_1382_2069))) in 
  let val wildcard_1013_1394_2081 = (print ")") in () end end end end end end end end end end end end
  | KDEmpty => 
  let val wildcard_1019_1395_2082 = (print "(KDEmpty") in 
  let val wildcard_1020_1396_2083 = (print ")") in () end end);

fun internal_traverse_KDTree (arg_928_1319_2006) = (case arg_928_1319_2006 of KDNode (x_929_1320_2007 , x_930_1321_2008, x_931_1322_2009, x_932_1323_2010, x_933_1324_2011, x_934_1325_2012, x_935_1326_2013, x_936_1327_2014, x_937_1328_2015, x_938_1329_2016, x_939_1330_2017, x_940_1331_2018) => 
  let val y_951_1332_2019 = (internal_traverse_KDTree x_939_1330_2017) in 
  let val y_952_1333_2020 = (internal_traverse_KDTree x_940_1331_2018) in () end end 
  | KDLeaf (x_953_1334_2021 , x_954_1335_2022, x_955_1336_2023, x_956_1337_2024, x_957_1338_2025) => ()
  | KDEmpty => ());

fun axisLowerBound (q_654_1316_2001 , lo_655_1317_2002, hi_656_1318_2003) = 
  let val fltIf_1568_2004 = (q_654_1316_2001 < lo_655_1317_2002) in 
  (if fltIf_1568_2004 then (lo_655_1317_2002 - q_654_1316_2001) 
   else 
  let val fltIf_1569_2005 = (q_654_1316_2001 > hi_656_1318_2003) in 
  (if fltIf_1569_2005 then (q_654_1316_2001 - hi_656_1318_2003) 
   else 0) end) end;

fun bboxLowerBound (minX_645_1307_1988 , minY_646_1308_1989, minZ_647_1309_1990, maxX_648_1310_1991, maxY_649_1311_1992, maxZ_650_1312_1993, qx_651_1313_1994, qy_652_1314_1995, qz_653_1315_1996) = 
  let val fltPrm_1565_1997 = (axisLowerBound(qx_651_1313_1994 , minX_645_1307_1988, maxX_648_1310_1991)) in 
  let val fltPrm_1566_1998 = (axisLowerBound(qy_652_1314_1995 , minY_646_1308_1989, maxY_649_1311_1992)) in 
  let val fltPrm_1564_1999 = (fltPrm_1565_1997 + fltPrm_1566_1998) in 
  let val fltPrm_1567_2000 = (axisLowerBound(qz_653_1315_1996 , minZ_647_1309_1990, maxZ_650_1312_1993)) in (fltPrm_1564_1999 + fltPrm_1567_2000) end end end end;

fun buildKD (d_639_1301_1969 , axis_640_1302_1970) = 
  let val fltIf_1551_1971 = (d_639_1301_1969 = 0) in 
  (if fltIf_1551_1971 then 
  let val fltPkd_1552_1972 = (d_639_1301_1969 + 1) in 
  let val fltPkd_1553_1973 = (d_639_1301_1969 + 2) in 
  let val fltPkd_1554_1974 = (d_639_1301_1969 * 3) in (KDLeaf (d_639_1301_1969 , fltPkd_1552_1972, fltPkd_1553_1973, fltPkd_1554_1974, d_639_1301_1969)) end end end 
   else 
  let val fltPrm_1555_1975 = (axis_640_1302_1970 + 1) in 
  let val nextAxis_641_1303_1976 = (fltPrm_1555_1975 mod 3) in 
  let val fltPrm_1556_1977 = (d_639_1301_1969 * 11) in 
  let val splitVal_642_1304_1978 = (fltPrm_1556_1977 + axis_640_1302_1970) in 
  let val fltAppE_1557_1979 = (d_639_1301_1969 - 1) in 
  let val l_643_1305_1980 = (buildKD(fltAppE_1557_1979 , nextAxis_641_1303_1976)) in 
  let val fltAppE_1558_1981 = (d_639_1301_1969 - 1) in 
  let val r_644_1306_1982 = (buildKD(fltAppE_1558_1981 , nextAxis_641_1303_1976)) in 
  let val fltPkd_1559_1983 = (0 - d_639_1301_1969) in 
  let val fltPkd_1560_1984 = (0 - d_639_1301_1969) in 
  let val fltPkd_1561_1985 = (0 - d_639_1301_1969) in 
  let val fltPkd_1562_1986 = (d_639_1301_1969 * 2) in 
  let val fltPkd_1563_1987 = (d_639_1301_1969 mod 2) in (KDNode (axis_640_1302_1970 , splitVal_642_1304_1978, fltPkd_1559_1983, fltPkd_1560_1984, fltPkd_1561_1985, d_639_1301_1969, d_639_1301_1969, d_639_1301_1969, fltPkd_1562_1986, fltPkd_1563_1987, l_643_1305_1980, r_644_1306_1982)) end end end end end end end end end end end end end) end;

fun bboxDisjoint (minX_570_1232_1887 , minY_571_1233_1888, minZ_572_1234_1889, maxX_573_1235_1890, maxY_574_1236_1891, maxZ_575_1237_1892, qMinX_576_1238_1893, qMaxX_577_1239_1894, qMinY_578_1240_1895, qMaxY_579_1241_1896, qMinZ_580_1242_1897, qMaxZ_581_1243_1898) = 
  let val fltIf_1538_1899 = (maxX_573_1235_1890 < qMinX_576_1238_1893) in 
  (if fltIf_1538_1899 then true 
   else 
  let val fltIf_1539_1900 = (minX_570_1232_1887 > qMaxX_577_1239_1894) in 
  (if fltIf_1539_1900 then true 
   else 
  let val fltIf_1540_1901 = (maxY_574_1236_1891 < qMinY_578_1240_1895) in 
  (if fltIf_1540_1901 then true 
   else 
  let val fltIf_1541_1902 = (minY_571_1233_1888 > qMaxY_579_1241_1896) in 
  (if fltIf_1541_1902 then true 
   else 
  let val fltIf_1542_1903 = (maxZ_575_1237_1892 < qMinZ_580_1242_1897) in 
  (if fltIf_1542_1903 then true 
   else 
  let val fltIf_1543_1904 = (minZ_572_1234_1889 > qMaxZ_581_1243_1898) in 
  (if fltIf_1543_1904 then true 
   else false) end) end) end) end) end) end;

fun absI (x_569_1231_1885) = 
  let val fltIf_1537_1886 = (x_569_1231_1885 < 0) in 
  (if fltIf_1537_1886 then (0 - x_569_1231_1885) 
   else x_569_1231_1885) end;

fun coordAt (axis_565_1227_1879 , x_566_1228_1880, y_567_1229_1881, z_568_1230_1882) = 
  let val fltIf_1535_1883 = (axis_565_1227_1879 = 0) in 
  (if fltIf_1535_1883 then x_566_1228_1880 
   else 
  let val fltIf_1536_1884 = (axis_565_1227_1879 = 1) in 
  (if fltIf_1536_1884 then y_567_1229_1881 
   else z_568_1230_1882) end) end;

fun minI (a_563_1225_1876 , b_564_1226_1877) = 
  let val fltIf_1534_1878 = (a_563_1225_1876 < b_564_1226_1877) in 
  (if fltIf_1534_1878 then a_563_1225_1876 
   else b_564_1226_1877) end;

fun dist3 (x1_519_1181_1806 , y1_520_1182_1807, z1_521_1183_1808, x2_522_1184_1809, y2_523_1185_1810, z2_524_1186_1811) = 
  let val fltAppE_1510_1812 = (x1_519_1181_1806 - x2_522_1184_1809) in 
  let val fltPrm_1509_1813 = (absI fltAppE_1510_1812) in 
  let val fltAppE_1512_1814 = (y1_520_1182_1807 - y2_523_1185_1810) in 
  let val fltPrm_1511_1815 = (absI fltAppE_1512_1814) in 
  let val fltPrm_1508_1816 = (fltPrm_1509_1813 + fltPrm_1511_1815) in 
  let val fltAppE_1514_1817 = (z1_521_1183_1808 - z2_524_1186_1811) in 
  let val fltPrm_1513_1818 = (absI fltAppE_1514_1817) in (fltPrm_1508_1816 + fltPrm_1513_1818) end end end end end end end;

fun photonMappingBenchmark (t_458_1120_1692 , phases_459_1121_1693, rays_460_1122_1694, seed_461_1123_1695, radius_462_1124_1696) = (case t_458_1120_1692 of KDLeaf (x_463_1125_1697 , y_464_1126_1698, z_465_1127_1699, wildcard__232_466_1128_1700, wildcard__233_467_1129_1701) => 
  let val fltIf_1455_1702 = (phases_459_1121_1693 = 0) in 
  let val active_468_1130_1704 = 
  (if fltIf_1455_1702 then 0 
   else 
  let val fltIf_1456_1703 = (rays_460_1122_1694 = 0) in 
  (if fltIf_1456_1703 then 0 
   else 1) end) in 
  let val fltPrm_1457_1705 = (seed_461_1123_1695 * 13) in 
  let val fltPrm_1458_1706 = (phases_459_1121_1693 * 7) in 
  let val ox_469_1131_1707 = (fltPrm_1457_1705 - fltPrm_1458_1706) in 
  let val fltPrm_1459_1708 = (seed_461_1123_1695 * 5) in 
  let val fltPrm_1460_1709 = (rays_460_1122_1694 * 3) in 
  let val oy_470_1132_1710 = (fltPrm_1459_1708 + fltPrm_1460_1709) in 
  let val fltPrm_1461_1711 = (seed_461_1123_1695 * 11) in 
  let val oz_471_1133_1712 = (fltPrm_1461_1711 - rays_460_1122_1694) in 
  let val d_472_1134_1713 = (dist3(x_463_1125_1697 , y_464_1126_1698, z_465_1127_1699, ox_469_1131_1707, oy_470_1132_1710, oz_471_1133_1712)) in 
  let val fltIf_1462_1714 = (d_472_1134_1713 <= radius_462_1124_1696) in 
  let val mHit_473_1135_1715 = 
  (if fltIf_1462_1714 then 1 
   else 0) in 
  let val fltPrm_1463_1716 = (active_468_1130_1704 * mHit_473_1135_1715) in (fltPrm_1463_1716 * rays_460_1122_1694) end end end end end end end end end end end end end end 
  | KDNode (splitDim_474_1136_1717 , splitVal_475_1137_1718, minX_476_1138_1719, minY_477_1139_1720, minZ_478_1140_1721, maxX_479_1141_1722, maxY_480_1142_1723, maxZ_481_1143_1724, wildcard__245_482_1144_1725, wildcard__246_483_1145_1726, l_484_1146_1727, r_485_1147_1728) => 
  let val fltIf_1464_1729 = (phases_459_1121_1693 = 0) in 
  let val active_486_1148_1731 = 
  (if fltIf_1464_1729 then 0 
   else 
  let val fltIf_1465_1730 = (rays_460_1122_1694 = 0) in 
  (if fltIf_1465_1730 then 0 
   else 1) end) in 
  let val fltPrm_1466_1732 = (seed_461_1123_1695 * 13) in 
  let val fltPrm_1467_1733 = (phases_459_1121_1693 * 7) in 
  let val ox_487_1149_1734 = (fltPrm_1466_1732 - fltPrm_1467_1733) in 
  let val fltPrm_1468_1735 = (seed_461_1123_1695 * 5) in 
  let val fltPrm_1469_1736 = (rays_460_1122_1694 * 3) in 
  let val oy_488_1150_1737 = (fltPrm_1468_1735 + fltPrm_1469_1736) in 
  let val fltPrm_1470_1738 = (seed_461_1123_1695 * 11) in 
  let val oz_489_1151_1739 = (fltPrm_1470_1738 - rays_460_1122_1694) in 
  let val fltPrm_1471_1740 = (seed_461_1123_1695 * 3) in 
  let val fltPrm_1472_1741 = (phases_459_1121_1693 * 2) in 
  let val dx_490_1152_1742 = (fltPrm_1471_1740 - fltPrm_1472_1741) in 
  let val fltPrm_1473_1743 = (seed_461_1123_1695 * 7) in 
  let val dy_491_1153_1744 = (fltPrm_1473_1743 - rays_460_1122_1694) in 
  let val fltPrm_1474_1745 = (seed_461_1123_1695 * 5) in 
  let val fltPrm_1475_1746 = (phases_459_1121_1693 + rays_460_1122_1694) in 
  let val dz_492_1154_1747 = (fltPrm_1474_1745 - fltPrm_1475_1746) in 
  let val oCoord_493_1155_1748 = (coordAt(splitDim_474_1136_1717 , ox_487_1149_1734, oy_488_1150_1737, oz_489_1151_1739)) in 
  let val dCoord_494_1156_1749 = (coordAt(splitDim_474_1136_1717 , dx_490_1152_1742, dy_491_1153_1744, dz_492_1154_1747)) in 
  let val fltAppE_1476_1750 = (oCoord_493_1155_1748 - splitVal_475_1137_1718) in 
  let val planeDist_495_1157_1751 = (absI fltAppE_1476_1750) in 
  let val boxDist_496_1158_1752 = (bboxLowerBound(minX_476_1138_1719 , minY_477_1139_1720, minZ_478_1140_1721, maxX_479_1141_1722, maxY_480_1142_1723, maxZ_481_1143_1724, ox_487_1149_1734, oy_488_1150_1737, oz_489_1151_1739)) in 
  let val reflected_497_1159_1753 = (rays_460_1122_1694 div 2) in 
  let val ior_i_498_1160_1754 = (2 + splitDim_474_1136_1717) in 
  let val fltPrm_1479_1755 = (splitVal_475_1137_1718 div 3) in 
  let val fltPrm_1478_1756 = (fltPrm_1479_1755 * 3) in 
  let val fltPrm_1477_1757 = (splitVal_475_1137_1718 - fltPrm_1478_1756) in 
  let val ior_t_499_1161_1758 = (1 + fltPrm_1477_1757) in 
  let val fltIf_1480_1759 = (ior_i_498_1160_1754 > ior_t_499_1161_1758) in 
  let val tir_500_1162_1763 = 
  (if fltIf_1480_1759 then 
  let val fltPrm_1482_1760 = (planeDist_495_1157_1751 * ior_i_498_1160_1754) in 
  let val fltPrm_1483_1761 = (radius_462_1124_1696 * ior_t_499_1161_1758) in 
  let val fltIf_1481_1762 = (fltPrm_1482_1760 > fltPrm_1483_1761) in 
  (if fltIf_1481_1762 then 1 
   else 0) end end end 
   else 0) in 
  let val fltIf_1484_1764 = (tir_500_1162_1763 = 1) in 
  let val refracted_501_1163_1765 = 
  (if fltIf_1484_1764 then 0 
   else (rays_460_1122_1694 div 3)) in 
  let val fltPrm_1485_1766 = (reflected_497_1159_1753 + refracted_501_1163_1765) in 
  let val nextRays_502_1164_1767 = (active_486_1148_1731 * fltPrm_1485_1766) in 
  let val fltIf_1486_1768 = (phases_459_1121_1693 > 0) in 
  let val nextPhase_503_1165_1769 = 
  (if fltIf_1486_1768 then (phases_459_1121_1693 - 1) 
   else 0) in 
  let val nextSeed_504_1166_1770 = (seed_461_1123_1695 + 17) in 
  let val fltIf_1487_1771 = (radius_462_1124_1696 > 3) in 
  let val nextRadius_505_1167_1772 = 
  (if fltIf_1487_1771 then (radius_462_1124_1696 - 3) 
   else 3) in 
  let val fltIf_1488_1773 = (dCoord_494_1156_1749 < 0) in 
  let val wildcard__259_506_1168_1774 = 
  (if fltIf_1488_1773 then (0 - dCoord_494_1156_1749) 
   else dCoord_494_1156_1749) in 
  let val hl_507_1169_1775 = (photonMappingBenchmark(l_484_1146_1727 , nextPhase_503_1165_1769, nextRays_502_1164_1767, nextSeed_504_1166_1770, nextRadius_505_1167_1772)) in 
  let val hr_508_1170_1776 = (photonMappingBenchmark(r_485_1147_1728 , nextPhase_503_1165_1769, nextRays_502_1164_1767, nextSeed_504_1166_1770, nextRadius_505_1167_1772)) in 
  let val fltIf_1489_1777 = (oCoord_493_1155_1748 < splitVal_475_1137_1718) in 
  let val side_509_1171_1778 = 
  (if fltIf_1489_1777 then 1 
   else 0) in 
  let val fltPrm_1490_1779 = (side_509_1171_1778 * hl_507_1169_1775) in 
  let val fltPrm_1492_1780 = (1 - side_509_1171_1778) in 
  let val fltPrm_1491_1781 = (fltPrm_1492_1780 * hr_508_1170_1776) in 
  let val near_510_1172_1782 = (fltPrm_1490_1779 + fltPrm_1491_1781) in 
  let val fltPrm_1493_1783 = (side_509_1171_1778 * hr_508_1170_1776) in 
  let val fltPrm_1495_1784 = (1 - side_509_1171_1778) in 
  let val fltPrm_1494_1785 = (fltPrm_1495_1784 * hl_507_1169_1775) in 
  let val far_511_1173_1786 = (fltPrm_1493_1783 + fltPrm_1494_1785) in 
  let val fltIf_1496_1787 = (boxDist_496_1158_1752 > radius_462_1124_1696) in 
  let val mBox_512_1174_1788 = 
  (if fltIf_1496_1787 then 0 
   else 1) in 
  let val fltIf_1497_1789 = (planeDist_495_1157_1751 <= radius_462_1124_1696) in 
  let val mPlane_513_1175_1790 = 
  (if fltIf_1497_1789 then 1 
   else 0) in 
  let val local_514_1176_1791 = (mBox_512_1174_1788 * rays_460_1122_1694) in 
  let val fltPrm_1500_1792 = (splitDim_474_1136_1717 div 2) in 
  let val fltPrm_1499_1793 = (fltPrm_1500_1792 * 2) in 
  let val fltPrm_1498_1794 = (splitDim_474_1136_1717 - fltPrm_1499_1793) in 
  let val kReflect_515_1177_1795 = (2 + fltPrm_1498_1794) in 
  let val fltIf_1501_1796 = (tir_500_1162_1763 = 1) in 
  let val kRefract_516_1178_1798 = 
  (if fltIf_1501_1796 then 0 
   else 
  let val fltPrm_1502_1797 = (ior_t_499_1161_1758 div 2) in (1 + fltPrm_1502_1797) end) in 
  let val fltPrm_1503_1799 = (kReflect_515_1177_1795 * near_510_1172_1782) in 
  let val reflectedTerm_517_1179_1800 = (fltPrm_1503_1799 div 3) in 
  let val fltPrm_1505_1801 = (kRefract_516_1178_1798 * mPlane_513_1175_1790) in 
  let val fltPrm_1504_1802 = (fltPrm_1505_1801 * far_511_1173_1786) in 
  let val refractedTerm_518_1180_1803 = (fltPrm_1504_1802 div 3) in 
  let val fltPrm_1507_1804 = (local_514_1176_1791 + reflectedTerm_517_1179_1800) in 
  let val fltPrm_1506_1805 = (fltPrm_1507_1804 + refractedTerm_518_1180_1803) in (active_486_1148_1731 * fltPrm_1506_1805) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end
  | KDEmpty => 0);

fun nearestDist (t_430_1092_1659 , qx_431_1093_1660, qy_432_1094_1661, qz_433_1095_1662) = (case t_430_1092_1659 of KDLeaf (x_434_1096_1663 , y_435_1097_1664, z_436_1098_1665, wildcard__48_437_1099_1666, wildcard__49_438_1100_1667) => (dist3(x_434_1096_1663 , y_435_1097_1664, z_436_1098_1665, qx_431_1093_1660, qy_432_1094_1661, qz_433_1095_1662)) 
  | KDNode (splitDim_439_1101_1668 , splitVal_440_1102_1669, minX_441_1103_1670, minY_442_1104_1671, minZ_443_1105_1672, maxX_444_1106_1673, maxY_445_1107_1674, maxZ_446_1108_1675, wildcard__55_447_1109_1676, wildcard__56_448_1110_1677, l_449_1111_1678, r_450_1112_1679) => 
  let val qCoord_451_1113_1680 = (coordAt(splitDim_439_1101_1668 , qx_431_1093_1660, qy_432_1094_1661, qz_433_1095_1662)) in 
  let val fltAppE_1450_1681 = (qCoord_451_1113_1680 - splitVal_440_1102_1669) in 
  let val planeDist_452_1114_1682 = (absI fltAppE_1450_1681) in 
  let val boxDist_453_1115_1683 = (bboxLowerBound(minX_441_1103_1670 , minY_442_1104_1671, minZ_443_1105_1672, maxX_444_1106_1673, maxY_445_1107_1674, maxZ_446_1108_1675, qx_431_1093_1660, qy_432_1094_1661, qz_433_1095_1662)) in 
  let val dl_454_1116_1684 = (nearestDist(l_449_1111_1678 , qx_431_1093_1660, qy_432_1094_1661, qz_433_1095_1662)) in 
  let val dr_455_1117_1685 = (nearestDist(r_450_1112_1679 , qx_431_1093_1660, qy_432_1094_1661, qz_433_1095_1662)) in 
  let val fltIf_1451_1686 = (qCoord_451_1113_1680 < splitVal_440_1102_1669) in 
  let val near_456_1118_1687 = 
  (if fltIf_1451_1686 then dl_454_1116_1684 
   else dr_455_1117_1685) in 
  let val fltIf_1452_1688 = (qCoord_451_1113_1680 < splitVal_440_1102_1669) in 
  let val far_457_1119_1689 = 
  (if fltIf_1452_1688 then dr_455_1117_1685 
   else dl_454_1116_1684) in 
  let val fltIf_1453_1690 = (boxDist_453_1115_1683 >= near_456_1118_1687) in 
  (if fltIf_1453_1690 then near_456_1118_1687 
   else 
  let val fltIf_1454_1691 = (planeDist_452_1114_1682 < near_456_1118_1687) in 
  (if fltIf_1454_1691 then (minI(near_456_1118_1687 , far_457_1119_1689)) 
   else near_456_1118_1687) end) end end end end end end end end end end end
  | KDEmpty => 1000000000);

fun pointCloudNeighborhood (t_403_1065_1629 , qx_404_1066_1630, qy_405_1067_1631, qz_406_1068_1632, radius_407_1069_1633) = (case t_403_1065_1629 of KDLeaf (x_408_1070_1634 , y_409_1071_1635, z_410_1072_1636, mass_411_1073_1637, oid_412_1074_1638) => 
  let val wildcard__202_413_1075_1639 = (mass_411_1073_1637 + oid_412_1074_1638) in 
  let val d_414_1076_1640 = (dist3(x_408_1070_1634 , y_409_1071_1635, z_410_1072_1636, qx_404_1066_1630, qy_405_1067_1631, qz_406_1068_1632)) in 
  let val fltIf_1447_1641 = (d_414_1076_1640 <= radius_407_1069_1633) in 
  (if fltIf_1447_1641 then 1 
   else 0) end end end 
  | KDNode (splitDim_415_1077_1642 , wildcard__209_416_1078_1643, minX_417_1079_1644, minY_418_1080_1645, minZ_419_1081_1646, maxX_420_1082_1647, maxY_421_1083_1648, maxZ_422_1084_1649, wildcard__210_423_1085_1650, wildcard__211_424_1086_1651, l_425_1087_1652, r_426_1088_1653) => 
  let val dMin_427_1089_1654 = (bboxLowerBound(minX_417_1079_1644 , minY_418_1080_1645, minZ_419_1081_1646, maxX_420_1082_1647, maxY_421_1083_1648, maxZ_422_1084_1649, qx_404_1066_1630, qy_405_1067_1631, qz_406_1068_1632)) in 
  let val cl_428_1090_1655 = (pointCloudNeighborhood(l_425_1087_1652 , qx_404_1066_1630, qy_405_1067_1631, qz_406_1068_1632, radius_407_1069_1633)) in 
  let val cr_429_1091_1656 = (pointCloudNeighborhood(r_426_1088_1653 , qx_404_1066_1630, qy_405_1067_1631, qz_406_1068_1632, radius_407_1069_1633)) in 
  let val fltIf_1448_1657 = (dMin_427_1089_1654 > radius_407_1069_1633) in 
  (if fltIf_1448_1657 then 0 
   else 
  let val fltIf_1449_1658 = (splitDim_415_1077_1642 = 0) in 
  (if fltIf_1449_1658 then (cl_428_1090_1655 + cr_429_1091_1656) 
   else (cr_429_1091_1656 + cl_428_1090_1655)) end) end end end end
  | KDEmpty => 0);

fun pointInBox (x_394_1056_1614 , y_395_1057_1615, z_396_1058_1616, qMinX_397_1059_1617, qMaxX_398_1060_1618, qMinY_399_1061_1619, qMaxY_400_1062_1620, qMinZ_401_1063_1621, qMaxZ_402_1064_1622) = 
  let val fltIf_1441_1623 = (x_394_1056_1614 < qMinX_397_1059_1617) in 
  (if fltIf_1441_1623 then false 
   else 
  let val fltIf_1442_1624 = (x_394_1056_1614 > qMaxX_398_1060_1618) in 
  (if fltIf_1442_1624 then false 
   else 
  let val fltIf_1443_1625 = (y_395_1057_1615 < qMinY_399_1061_1619) in 
  (if fltIf_1443_1625 then false 
   else 
  let val fltIf_1444_1626 = (y_395_1057_1615 > qMaxY_400_1062_1620) in 
  (if fltIf_1444_1626 then false 
   else 
  let val fltIf_1445_1627 = (z_396_1058_1616 < qMinZ_401_1063_1621) in 
  (if fltIf_1445_1627 then false 
   else 
  let val fltIf_1446_1628 = (z_396_1058_1616 > qMaxZ_402_1064_1622) in 
  (if fltIf_1446_1628 then false 
   else true) end) end) end) end) end) end;

fun sumMassInRange (t_525_1187_1819 , qMinX_526_1188_1820, qMaxX_527_1189_1821, qMinY_528_1190_1822, qMaxY_529_1191_1823, qMinZ_530_1192_1824, qMaxZ_531_1193_1825) = (case t_525_1187_1819 of KDLeaf (x_532_1194_1826 , y_533_1195_1827, z_534_1196_1828, mass_535_1197_1829, wildcard__137_536_1198_1830) => 
  let val fltIf_1515_1831 = (pointInBox(x_532_1194_1826 , y_533_1195_1827, z_534_1196_1828, qMinX_526_1188_1820, qMaxX_527_1189_1821, qMinY_528_1190_1822, qMaxY_529_1191_1823, qMinZ_530_1192_1824, qMaxZ_531_1193_1825)) in 
  (if fltIf_1515_1831 then mass_535_1197_1829 
   else 0) end 
  | KDNode (splitDim_537_1199_1832 , splitVal_538_1200_1833, minX_539_1201_1834, minY_540_1202_1835, minZ_541_1203_1836, maxX_542_1204_1837, maxY_543_1205_1838, maxZ_544_1206_1839, wildcard__143_545_1207_1840, wildcard__144_546_1208_1841, l_547_1209_1842, r_548_1210_1843) => 
  let val disjoint_549_1211_1844 = (bboxDisjoint(minX_539_1201_1834 , minY_540_1202_1835, minZ_541_1203_1836, maxX_542_1204_1837, maxY_543_1205_1838, maxZ_544_1206_1839, qMinX_526_1188_1820, qMaxX_527_1189_1821, qMinY_528_1190_1822, qMaxY_529_1191_1823, qMinZ_530_1192_1824, qMaxZ_531_1193_1825)) in 
  let val qLo_550_1212_1845 = (coordAt(splitDim_537_1199_1832 , qMinX_526_1188_1820, qMinY_528_1190_1822, qMinZ_530_1192_1824)) in 
  let val qHi_551_1213_1846 = (coordAt(splitDim_537_1199_1832 , qMaxX_527_1189_1821, qMaxY_529_1191_1823, qMaxZ_531_1193_1825)) in 
  let val ml_552_1214_1847 = (sumMassInRange(l_547_1209_1842 , qMinX_526_1188_1820, qMaxX_527_1189_1821, qMinY_528_1190_1822, qMaxY_529_1191_1823, qMinZ_530_1192_1824, qMaxZ_531_1193_1825)) in 
  let val mr_553_1215_1848 = (sumMassInRange(r_548_1210_1843 , qMinX_526_1188_1820, qMaxX_527_1189_1821, qMinY_528_1190_1822, qMaxY_529_1191_1823, qMinZ_530_1192_1824, qMaxZ_531_1193_1825)) in 
  (if disjoint_549_1211_1844 then 0 
   else 
  let val fltIf_1516_1849 = (qHi_551_1213_1846 < splitVal_538_1200_1833) in 
  (if fltIf_1516_1849 then ml_552_1214_1847 
   else 
  let val fltIf_1517_1850 = (qLo_550_1212_1845 > splitVal_538_1200_1833) in 
  (if fltIf_1517_1850 then mr_553_1215_1848 
   else (ml_552_1214_1847 + mr_553_1215_1848)) end) end) end end end end end);

fun countInRange (t_610_1272_1937 , qMinX_611_1273_1938, qMaxX_612_1274_1939, qMinY_613_1275_1940, qMaxY_614_1276_1941, qMinZ_615_1277_1942, qMaxZ_616_1278_1943) = (case t_610_1272_1937 of KDLeaf (x_617_1279_1944 , y_618_1280_1945, z_619_1281_1946, wildcard__104_620_1282_1947, wildcard__105_621_1283_1948) => 
  let val fltIf_1548_1949 = (pointInBox(x_617_1279_1944 , y_618_1280_1945, z_619_1281_1946, qMinX_611_1273_1938, qMaxX_612_1274_1939, qMinY_613_1275_1940, qMaxY_614_1276_1941, qMinZ_615_1277_1942, qMaxZ_616_1278_1943)) in 
  (if fltIf_1548_1949 then 1 
   else 0) end 
  | KDNode (splitDim_622_1284_1950 , splitVal_623_1285_1951, minX_624_1286_1952, minY_625_1287_1953, minZ_626_1288_1954, maxX_627_1289_1955, maxY_628_1290_1956, maxZ_629_1291_1957, wildcard__111_630_1292_1958, wildcard__112_631_1293_1959, l_632_1294_1960, r_633_1295_1961) => 
  let val disjoint_634_1296_1962 = (bboxDisjoint(minX_624_1286_1952 , minY_625_1287_1953, minZ_626_1288_1954, maxX_627_1289_1955, maxY_628_1290_1956, maxZ_629_1291_1957, qMinX_611_1273_1938, qMaxX_612_1274_1939, qMinY_613_1275_1940, qMaxY_614_1276_1941, qMinZ_615_1277_1942, qMaxZ_616_1278_1943)) in 
  let val qLo_635_1297_1963 = (coordAt(splitDim_622_1284_1950 , qMinX_611_1273_1938, qMinY_613_1275_1940, qMinZ_615_1277_1942)) in 
  let val qHi_636_1298_1964 = (coordAt(splitDim_622_1284_1950 , qMaxX_612_1274_1939, qMaxY_614_1276_1941, qMaxZ_616_1278_1943)) in 
  let val cl_637_1299_1965 = (countInRange(l_632_1294_1960 , qMinX_611_1273_1938, qMaxX_612_1274_1939, qMinY_613_1275_1940, qMaxY_614_1276_1941, qMinZ_615_1277_1942, qMaxZ_616_1278_1943)) in 
  let val cr_638_1300_1966 = (countInRange(r_633_1295_1961 , qMinX_611_1273_1938, qMaxX_612_1274_1939, qMinY_613_1275_1940, qMaxY_614_1276_1941, qMinZ_615_1277_1942, qMaxZ_616_1278_1943)) in 
  (if disjoint_634_1296_1962 then 0 
   else 
  let val fltIf_1549_1967 = (qHi_636_1298_1964 < splitVal_623_1285_1951) in 
  (if fltIf_1549_1967 then cl_637_1299_1965 
   else 
  let val fltIf_1550_1968 = (qLo_635_1297_1963 > splitVal_623_1285_1951) in 
  (if fltIf_1550_1968 then cr_638_1300_1966 
   else (cl_637_1299_1965 + cr_638_1300_1966)) end) end) end end end end end
  | KDEmpty => 0);

fun maxI (a_392_1054_1611 , b_393_1055_1612) = 
  let val fltIf_1440_1613 = (a_392_1054_1611 > b_393_1055_1612) in 
  (if fltIf_1440_1613 then a_392_1054_1611 
   else b_393_1055_1612) end;

fun bboxUpperBound (minX_554_1216_1851 , minY_555_1217_1852, minZ_556_1218_1853, maxX_557_1219_1854, maxY_558_1220_1855, maxZ_559_1221_1856, qx_560_1222_1857, qy_561_1223_1858, qz_562_1224_1859) = 
  let val fltAppE_1521_1860 = (qx_560_1222_1857 - minX_554_1216_1851) in 
  let val fltAppE_1520_1861 = (absI fltAppE_1521_1860) in 
  let val fltAppE_1523_1862 = (qx_560_1222_1857 - maxX_557_1219_1854) in 
  let val fltAppE_1522_1863 = (absI fltAppE_1523_1862) in 
  let val fltPrm_1519_1864 = (maxI(fltAppE_1520_1861 , fltAppE_1522_1863)) in 
  let val fltAppE_1526_1865 = (qy_561_1223_1858 - minY_555_1217_1852) in 
  let val fltAppE_1525_1866 = (absI fltAppE_1526_1865) in 
  let val fltAppE_1528_1867 = (qy_561_1223_1858 - maxY_558_1220_1855) in 
  let val fltAppE_1527_1868 = (absI fltAppE_1528_1867) in 
  let val fltPrm_1524_1869 = (maxI(fltAppE_1525_1866 , fltAppE_1527_1868)) in 
  let val fltPrm_1518_1870 = (fltPrm_1519_1864 + fltPrm_1524_1869) in 
  let val fltAppE_1531_1871 = (qz_562_1224_1859 - minZ_556_1218_1853) in 
  let val fltAppE_1530_1872 = (absI fltAppE_1531_1871) in 
  let val fltAppE_1533_1873 = (qz_562_1224_1859 - maxZ_559_1221_1856) in 
  let val fltAppE_1532_1874 = (absI fltAppE_1533_1873) in 
  let val fltPrm_1529_1875 = (maxI(fltAppE_1530_1872 , fltAppE_1532_1874)) in (fltPrm_1518_1870 + fltPrm_1529_1875) end end end end end end end end end end end end end end end end;

fun twoPointCorrelation (t_582_1244_1905 , qx_583_1245_1906, qy_584_1246_1907, qz_585_1247_1908, rLo_586_1248_1909, rHi_587_1249_1910) = (case t_582_1244_1905 of KDLeaf (x_588_1250_1911 , y_589_1251_1912, z_590_1252_1913, wildcard__168_591_1253_1914, wildcard__169_592_1254_1915) => 
  let val d_593_1255_1916 = (dist3(x_588_1250_1911 , y_589_1251_1912, z_590_1252_1913, qx_583_1245_1906, qy_584_1246_1907, qz_585_1247_1908)) in 
  let val fltIf_1544_1917 = (d_593_1255_1916 < rLo_586_1248_1909) in 
  (if fltIf_1544_1917 then 0 
   else 
  let val fltIf_1545_1918 = (d_593_1255_1916 > rHi_587_1249_1910) in 
  (if fltIf_1545_1918 then 0 
   else 1) end) end end 
  | KDNode (wildcard__176_594_1256_1919 , wildcard__177_595_1257_1920, minX_596_1258_1921, minY_597_1259_1922, minZ_598_1260_1923, maxX_599_1261_1924, maxY_600_1262_1925, maxZ_601_1263_1926, wildcard__178_602_1264_1927, wildcard__179_603_1265_1928, l_604_1266_1929, r_605_1267_1930) => 
  let val dMin_606_1268_1931 = (bboxLowerBound(minX_596_1258_1921 , minY_597_1259_1922, minZ_598_1260_1923, maxX_599_1261_1924, maxY_600_1262_1925, maxZ_601_1263_1926, qx_583_1245_1906, qy_584_1246_1907, qz_585_1247_1908)) in 
  let val dMax_607_1269_1932 = (bboxUpperBound(minX_596_1258_1921 , minY_597_1259_1922, minZ_598_1260_1923, maxX_599_1261_1924, maxY_600_1262_1925, maxZ_601_1263_1926, qx_583_1245_1906, qy_584_1246_1907, qz_585_1247_1908)) in 
  let val cl_608_1270_1933 = (twoPointCorrelation(l_604_1266_1929 , qx_583_1245_1906, qy_584_1246_1907, qz_585_1247_1908, rLo_586_1248_1909, rHi_587_1249_1910)) in 
  let val cr_609_1271_1934 = (twoPointCorrelation(r_605_1267_1930 , qx_583_1245_1906, qy_584_1246_1907, qz_585_1247_1908, rLo_586_1248_1909, rHi_587_1249_1910)) in 
  let val fltIf_1546_1935 = (dMin_606_1268_1931 > rHi_587_1249_1910) in 
  (if fltIf_1546_1935 then 0 
   else 
  let val fltIf_1547_1936 = (dMax_607_1269_1932 < rLo_586_1248_1909) in 
  (if fltIf_1547_1936 then 0 
   else (cl_608_1270_1933 + cr_609_1271_1934)) end) end end end end end
  | KDEmpty => 0);
val _ = (case 
  let val wildcard__356_359_1021_1570 = (printsym "Running program KDTree: ") in 
  let val wildcard__354_360_1022_1571 = (printsym "NEWLINE") in 
  let val fltPrm_1433_1572 = (GibbonCompat.getSizeParam()) in 
  let val fltAppE_1432_1573 = (fltPrm_1433_1572 + 22) in 
  let val kdTree_361_1023_1574 = (buildKD(fltAppE_1432_1573 , 0)) in 
  let val wildcard__351_362_1024_1575 = (printsym "Running pass Find nearest Neighbour (fold_like, uses=13): ") in 
  let val wildcard__349_363_1025_1576 = (printsym "NEWLINE") in 
  let val dist_364_1026_1577 = (iterate (fn () => nearestDist(kdTree_361_1023_1574 , 1, 2, 3))) in 
  let val wildcard__345_365_1027_1578 = (printsym "End") in 
  let val wildcard__343_366_1028_1579 = (printsym "NEWLINE") in 
  let val wildcard__341_367_1029_1580 = (printsym "Running pass countInRange tight_box (fold_like, uses=13): ") in 
  let val wildcard__339_368_1030_1581 = (printsym "NEWLINE") in 
  let val inRangeCount_369_1031_1585 = 
  let val fltAppE_1434_1582 = (iterate (fn () => 0 - 20)) in 
  let val fltAppE_1435_1583 = (0 - 12) in 
  let val fltAppE_1436_1584 = (0 - 7) in (countInRange(kdTree_361_1023_1574 , fltAppE_1434_1582, 20, fltAppE_1435_1583, 12, fltAppE_1436_1584, 7)) end end end in 
  let val wildcard__335_370_1032_1586 = (printsym "End") in 
  let val wildcard__333_371_1033_1587 = (printsym "NEWLINE") in 
  let val wildcard__331_372_1034_1588 = (printsym "Running pass sumMassInRange (fold_like, uses=14): ") in 
  let val wildcard__329_373_1035_1589 = (printsym "NEWLINE") in 
  let val massInRange_374_1036_1593 = 
  let val fltAppE_1437_1590 = (iterate (fn () => 0 - 25)) in 
  let val fltAppE_1438_1591 = (0 - 20) in 
  let val fltAppE_1439_1592 = (0 - 15) in (sumMassInRange(kdTree_361_1023_1574 , fltAppE_1437_1590, 25, fltAppE_1438_1591, 20, fltAppE_1439_1592, 15)) end end end in 
  let val wildcard__325_375_1037_1594 = (printsym "End") in 
  let val wildcard__323_376_1038_1595 = (printsym "NEWLINE") in 
  let val wildcard__321_377_1039_1596 = (printsym "Running pass twoPointCorrelation bin_8_16 (fold_like, uses=11): ") in 
  let val wildcard__319_378_1040_1597 = (printsym "NEWLINE") in 
  let val corrCount_379_1041_1598 = (iterate (fn () => twoPointCorrelation(kdTree_361_1023_1574 , 0, 0, 0, 8, 16))) in 
  let val wildcard__315_380_1042_1599 = (printsym "End") in 
  let val wildcard__313_381_1043_1600 = (printsym "NEWLINE") in 
  let val wildcard__311_382_1044_1601 = (printsym "Running pass pointCloudNeighborhood (fold_like, uses=11): ") in 
  let val wildcard__309_383_1045_1602 = (printsym "NEWLINE") in 
  let val cloudCount_384_1046_1603 = (iterate (fn () => pointCloudNeighborhood(kdTree_361_1023_1574 , 0, 0, 0, 24))) in 
  let val wildcard__305_385_1047_1604 = (printsym "End") in 
  let val wildcard__303_386_1048_1605 = (printsym "NEWLINE") in 
  let val wildcard__301_387_1049_1606 = (printsym "Running pass photonMappingBenchmark (fold_like, uses=12): ") in 
  let val wildcard__299_388_1050_1607 = (printsym "NEWLINE") in 
  let val photonHits_389_1051_1608 = (iterate (fn () => photonMappingBenchmark(kdTree_361_1023_1574 , 5, 16, 7, 18))) in 
  let val wildcard__295_390_1052_1609 = (printsym "End") in 
  let val wildcard__293_391_1053_1610 = (printsym "NEWLINE") in (dist_364_1026_1577 , inRangeCount_369_1031_1585, massInRange_374_1036_1593, corrCount_379_1041_1598, cloudCount_384_1046_1603, photonHits_389_1051_1608) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end of (x__1 , x__2, x__3, x__4, x__5, x__6) => let val _ = print "#(" val _ = (print(Int.toString(x__1))) val _ = print " "val _ = (print(Int.toString(x__2))) val _ = print " "val _ = (print(Int.toString(x__3))) val _ = print " "val _ = (print(Int.toString(x__4))) val _ = print " "val _ = (print(Int.toString(x__5))) val _ = print " "val _ = (print(Int.toString(x__6))) val _ = print ")" in () end);
val _ = print "\n"
