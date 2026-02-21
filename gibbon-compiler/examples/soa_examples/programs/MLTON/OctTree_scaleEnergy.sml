open GibbonCompat;

datatype dat_Octree = Cell of (int  * int * int * int * int *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree) | Particle of (int  * int * int)| EmptyOct ;

fun scaleEnergy (t_306_1425_1901 , k_307_1426_1902) = (case t_306_1425_1901 of Cell (m_308_1427_1903 , c_309_1428_1904, n_310_1429_1905, s_311_1430_1906, mom_312_1431_1907, a_313_1432_1908, b_314_1433_1909, c1_315_1434_1910, d_316_1435_1911, e_317_1436_1912, f_318_1437_1913, g_319_1438_1914, h_320_1439_1915) => 
  let val fltPrm_1537_1916 = (mom_312_1431_1907 * k_307_1426_1902) in 
  let val fltPrm_1538_1917 = (s_311_1430_1906 + 1) in 
  let val mom__321_1440_1918 = (fltPrm_1537_1916 div fltPrm_1538_1917) in 
  let val fltPkd_1539_1919 = (scaleEnergy(a_313_1432_1908 , k_307_1426_1902)) in 
  let val fltPkd_1540_1920 = (scaleEnergy(b_314_1433_1909 , k_307_1426_1902)) in 
  let val fltPkd_1541_1921 = (scaleEnergy(c1_315_1434_1910 , k_307_1426_1902)) in 
  let val fltPkd_1542_1922 = (scaleEnergy(d_316_1435_1911 , k_307_1426_1902)) in 
  let val fltPkd_1543_1923 = (scaleEnergy(e_317_1436_1912 , k_307_1426_1902)) in 
  let val fltPkd_1544_1924 = (scaleEnergy(f_318_1437_1913 , k_307_1426_1902)) in 
  let val fltPkd_1545_1925 = (scaleEnergy(g_319_1438_1914 , k_307_1426_1902)) in 
  let val fltPkd_1546_1926 = (scaleEnergy(h_320_1439_1915 , k_307_1426_1902)) in (Cell (m_308_1427_1903 , c_309_1428_1904, n_310_1429_1905, s_311_1430_1906, mom__321_1440_1918, fltPkd_1539_1919, fltPkd_1540_1920, fltPkd_1541_1921, fltPkd_1542_1922, fltPkd_1543_1923, fltPkd_1544_1924, fltPkd_1545_1925, fltPkd_1546_1926)) end end end end end end end end end end end 
  | Particle (m_322_1441_1927 , p_323_1442_1928, v_324_1443_1929) => 
  let val fltPrm_1547_1930 = (v_324_1443_1929 * k_307_1426_1902) in 
  let val v__325_1444_1931 = (fltPrm_1547_1930 div 10) in (Particle (m_322_1441_1927 , p_323_1442_1928, v__325_1444_1931)) end end
  | EmptyOct => EmptyOct);

fun maxI (a_304_1423_1898 , b_305_1424_1899) = 
  let val fltIf_1536_1900 = (a_304_1423_1898 > b_305_1424_1899) in 
  (if fltIf_1536_1900 then a_304_1423_1898 
   else b_305_1424_1899) end;

fun momentumOf (t_287_1406_1881) = (case t_287_1406_1881 of Cell (wildcard__106_288_1407_1882 , wildcard__107_289_1408_1883, wildcard__108_290_1409_1884, wildcard__109_291_1410_1885, mom_292_1411_1886, wildcard__110_293_1412_1887, wildcard__111_294_1413_1888, wildcard__112_295_1414_1889, wildcard__113_296_1415_1890, wildcard__114_297_1416_1891, wildcard__115_298_1417_1892, wildcard__116_299_1418_1893, wildcard__117_300_1419_1894) => mom_292_1411_1886 
  | Particle (m_301_1420_1895 , wildcard__131_302_1421_1896, v_303_1422_1897) => (m_301_1420_1895 * v_303_1422_1897)
  | EmptyOct => 0);

fun sum8 (a_241_1360_1767 , b_242_1361_1768, c_243_1362_1769, d_244_1363_1770, e_245_1364_1771, f_246_1365_1772, g_247_1366_1773, h_248_1367_1774) = 
  let val fltPrm_1473_1775 = (a_241_1360_1767 + b_242_1361_1768) in 
  let val fltPrm_1472_1776 = (fltPrm_1473_1775 + c_243_1362_1769) in 
  let val fltPrm_1471_1777 = (fltPrm_1472_1776 + d_244_1363_1770) in 
  let val fltPrm_1470_1778 = (fltPrm_1471_1777 + e_245_1364_1771) in 
  let val fltPrm_1469_1779 = (fltPrm_1470_1778 + f_246_1365_1772) in 
  let val fltPrm_1468_1780 = (fltPrm_1469_1779 + g_247_1366_1773) in (fltPrm_1468_1780 + h_248_1367_1774) end end end end end end;

fun absI (x_240_1359_1765) = 
  let val fltIf_1467_1766 = (x_240_1359_1765 < 0) in 
  (if fltIf_1467_1766 then (0 - x_240_1359_1765) 
   else x_240_1359_1765) end;

fun mixSeed (s_230_1349_1760 , salt_231_1350_1761) = 
  let val fltPrm_1465_1762 = (s_230_1349_1760 * 1103) in 
  let val fltPrm_1466_1763 = (salt_231_1350_1761 * 97) in 
  let val fltPrm_1464_1764 = (fltPrm_1465_1762 + fltPrm_1466_1763) in (fltPrm_1464_1764 + 13) end end end;

fun internal_traverse_Octree (arg_935_1236_1735) = (case arg_935_1236_1735 of Cell (x_936_1237_1736 , x_937_1238_1737, x_938_1239_1738, x_939_1240_1739, x_940_1241_1740, x_941_1242_1741, x_942_1243_1742, x_943_1244_1743, x_944_1245_1744, x_945_1246_1745, x_946_1247_1746, x_947_1248_1747, x_948_1249_1748) => 
  let val y_954_1250_1749 = (internal_traverse_Octree x_941_1242_1741) in 
  let val y_955_1251_1750 = (internal_traverse_Octree x_942_1243_1742) in 
  let val y_956_1252_1751 = (internal_traverse_Octree x_943_1244_1743) in 
  let val y_957_1253_1752 = (internal_traverse_Octree x_944_1245_1744) in 
  let val y_958_1254_1753 = (internal_traverse_Octree x_945_1246_1745) in 
  let val y_959_1255_1754 = (internal_traverse_Octree x_946_1247_1746) in 
  let val y_960_1256_1755 = (internal_traverse_Octree x_947_1248_1747) in 
  let val y_961_1257_1756 = (internal_traverse_Octree x_948_1249_1748) in () end end end end end end end end 
  | Particle (x_962_1258_1757 , x_963_1259_1758, x_964_1260_1759) => ()
  | EmptyOct => ());

fun internal_print_Octree (arg_968_1181_1680) = (case arg_968_1181_1680 of Cell (x_969_1182_1681 , x_970_1183_1682, x_971_1184_1683, x_972_1185_1684, x_973_1186_1685, x_974_1187_1686, x_975_1188_1687, x_976_1189_1688, x_977_1190_1689, x_978_1191_1690, x_979_1192_1691, x_980_1193_1692, x_981_1194_1693) => 
  let val wildcard_995_1195_1694 = (print "(Cell") in 
  let val wildcard_1009_1196_1695 = (print " ") in 
  let val y_982_1197_1696 = (print(Int.toString(x_969_1182_1681))) in 
  let val wildcard_1008_1198_1697 = (print " ") in 
  let val y_983_1199_1698 = (print(Int.toString(x_970_1183_1682))) in 
  let val wildcard_1007_1200_1699 = (print " ") in 
  let val y_984_1201_1700 = (print(Int.toString(x_971_1184_1683))) in 
  let val wildcard_1006_1202_1701 = (print " ") in 
  let val y_985_1203_1702 = (print(Int.toString(x_972_1185_1684))) in 
  let val wildcard_1005_1204_1703 = (print " ") in 
  let val y_986_1205_1704 = (print(Int.toString(x_973_1186_1685))) in 
  let val wildcard_1004_1206_1705 = (print " ") in 
  let val y_987_1207_1706 = (internal_print_Octree x_974_1187_1686) in 
  let val wildcard_1003_1208_1707 = (print " ") in 
  let val y_988_1209_1708 = (internal_print_Octree x_975_1188_1687) in 
  let val wildcard_1002_1210_1709 = (print " ") in 
  let val y_989_1211_1710 = (internal_print_Octree x_976_1189_1688) in 
  let val wildcard_1001_1212_1711 = (print " ") in 
  let val y_990_1213_1712 = (internal_print_Octree x_977_1190_1689) in 
  let val wildcard_1000_1214_1713 = (print " ") in 
  let val y_991_1215_1714 = (internal_print_Octree x_978_1191_1690) in 
  let val wildcard_999_1216_1715 = (print " ") in 
  let val y_992_1217_1716 = (internal_print_Octree x_979_1192_1691) in 
  let val wildcard_998_1218_1717 = (print " ") in 
  let val y_993_1219_1718 = (internal_print_Octree x_980_1193_1692) in 
  let val wildcard_997_1220_1719 = (print " ") in 
  let val y_994_1221_1720 = (internal_print_Octree x_981_1194_1693) in 
  let val wildcard_996_1222_1721 = (print ")") in () end end end end end end end end end end end end end end end end end end end end end end end end end end end end 
  | Particle (x_1010_1223_1722 , x_1011_1224_1723, x_1012_1225_1724) => 
  let val wildcard_1016_1226_1725 = (print "(Particle") in 
  let val wildcard_1020_1227_1726 = (print " ") in 
  let val y_1013_1228_1727 = (print(Int.toString(x_1010_1223_1722))) in 
  let val wildcard_1019_1229_1728 = (print " ") in 
  let val y_1014_1230_1729 = (print(Int.toString(x_1011_1224_1723))) in 
  let val wildcard_1018_1231_1730 = (print " ") in 
  let val y_1015_1232_1731 = (print(Int.toString(x_1012_1225_1724))) in 
  let val wildcard_1017_1233_1732 = (print ")") in () end end end end end end end end
  | EmptyOct => 
  let val wildcard_1021_1234_1733 = (print "(EmptyOct") in 
  let val wildcard_1022_1235_1734 = (print ")") in () end end);

fun massOf (t_125_1164_1663) = (case t_125_1164_1663 of Cell (m_126_1165_1664 , wildcard__14_127_1166_1665, wildcard__15_128_1167_1666, wildcard__16_129_1168_1667, wildcard__17_130_1169_1668, wildcard__18_131_1170_1669, wildcard__19_132_1171_1670, wildcard__20_133_1172_1671, wildcard__21_134_1173_1672, wildcard__22_135_1174_1673, wildcard__23_136_1175_1674, wildcard__24_137_1176_1675, wildcard__25_138_1177_1676) => m_126_1165_1664 
  | Particle (m_139_1178_1677 , wildcard__39_140_1179_1678, wildcard__40_141_1180_1679) => m_139_1178_1677
  | EmptyOct => 0);

fun weightedPos (t_108_1147_1646) = (case t_108_1147_1646 of Cell (m_109_1148_1647 , c_110_1149_1648, wildcard__45_111_1150_1649, wildcard__46_112_1151_1650, wildcard__47_113_1152_1651, wildcard__48_114_1153_1652, wildcard__49_115_1154_1653, wildcard__50_116_1155_1654, wildcard__51_117_1156_1655, wildcard__52_118_1157_1656, wildcard__53_119_1158_1657, wildcard__54_120_1159_1658, wildcard__55_121_1160_1659) => (m_109_1148_1647 * c_110_1149_1648) 
  | Particle (m_122_1161_1660 , p_123_1162_1661, wildcard__69_124_1163_1662) => (m_122_1161_1660 * p_123_1162_1661)
  | EmptyOct => 0);

fun countOf (t_46_1085_1629) = (case t_46_1085_1629 of Cell (wildcard__74_47_1086_1630 , wildcard__75_48_1087_1631, n_49_1088_1632, wildcard__76_50_1089_1633, wildcard__77_51_1090_1634, wildcard__78_52_1091_1635, wildcard__79_53_1092_1636, wildcard__80_54_1093_1637, wildcard__81_55_1094_1638, wildcard__82_56_1095_1639, wildcard__83_57_1096_1640, wildcard__84_58_1097_1641, wildcard__85_59_1098_1642) => n_49_1088_1632 
  | Particle (wildcard__99_60_1099_1643 , wildcard__100_61_1100_1644, wildcard__101_62_1101_1645) => 1
  | EmptyOct => 0);

fun buildOctree (d_249_1368_1781 , seed_250_1369_1782, center_251_1370_1783, half_252_1371_1784) = 
  let val fltIf_1474_1785 = (d_249_1368_1781 = 0) in 
  (if fltIf_1474_1785 then 
  let val fltPrm_1476_1786 = (absI seed_250_1369_1782) in 
  let val fltPrm_1475_1787 = (fltPrm_1476_1786 mod 5) in 
  let val m_253_1372_1788 = (1 + fltPrm_1475_1787) in 
  let val fltPrm_1479_1789 = (mixSeed(seed_250_1369_1782 , 3)) in 
  let val fltPrm_1478_1790 = (fltPrm_1479_1789 mod 3) in 
  let val fltPrm_1477_1791 = (center_251_1370_1783 + fltPrm_1478_1790) in 
  let val p_254_1373_1792 = (fltPrm_1477_1791 - 1) in 
  let val fltPrm_1481_1793 = (mixSeed(seed_250_1369_1782 , 11)) in 
  let val fltPrm_1480_1794 = (fltPrm_1481_1793 mod 11) in 
  let val v_255_1374_1795 = (fltPrm_1480_1794 - 5) in (Particle (m_253_1372_1788 , p_254_1373_1792, v_255_1374_1795)) end end end end end end end end end end 
   else 
  let val fltAppE_1482_1796 = (half_252_1371_1784 div 2) in 
  let val half__256_1375_1797 = (maxI(1 , fltAppE_1482_1796)) in 
  let val fltAppE_1483_1798 = (half_252_1371_1784 div 4) in 
  let val stride_257_1376_1799 = (maxI(1 , fltAppE_1483_1798)) in 
  let val fltPrm_1484_1800 = (stride_257_1376_1799 * 7) in 
  let val o0_258_1377_1801 = (0 - fltPrm_1484_1800) in 
  let val fltPrm_1485_1802 = (stride_257_1376_1799 * 5) in 
  let val o1_259_1378_1803 = (0 - fltPrm_1485_1802) in 
  let val fltPrm_1486_1804 = (stride_257_1376_1799 * 3) in 
  let val o2_260_1379_1805 = (0 - fltPrm_1486_1804) in 
  let val o3_261_1380_1806 = (0 - stride_257_1376_1799) in 
  let val o5_263_1382_1808 = (stride_257_1376_1799 * 3) in 
  let val o6_264_1383_1809 = (stride_257_1376_1799 * 5) in 
  let val o7_265_1384_1810 = (stride_257_1376_1799 * 7) in 
  let val fltAppE_1487_1811 = (d_249_1368_1781 - 1) in 
  let val fltAppE_1488_1812 = (mixSeed(seed_250_1369_1782 , 1)) in 
  let val fltAppE_1489_1813 = (center_251_1370_1783 + o0_258_1377_1801) in 
  let val c0_266_1385_1814 = (buildOctree(fltAppE_1487_1811 , fltAppE_1488_1812, fltAppE_1489_1813, half__256_1375_1797)) in 
  let val fltAppE_1490_1815 = (d_249_1368_1781 - 1) in 
  let val fltAppE_1491_1816 = (mixSeed(seed_250_1369_1782 , 2)) in 
  let val fltAppE_1492_1817 = (center_251_1370_1783 + o1_259_1378_1803) in 
  let val c1_267_1386_1818 = (buildOctree(fltAppE_1490_1815 , fltAppE_1491_1816, fltAppE_1492_1817, half__256_1375_1797)) in 
  let val fltAppE_1493_1819 = (d_249_1368_1781 - 1) in 
  let val fltAppE_1494_1820 = (mixSeed(seed_250_1369_1782 , 3)) in 
  let val fltAppE_1495_1821 = (center_251_1370_1783 + o2_260_1379_1805) in 
  let val c2_268_1387_1822 = (buildOctree(fltAppE_1493_1819 , fltAppE_1494_1820, fltAppE_1495_1821, half__256_1375_1797)) in 
  let val fltAppE_1496_1823 = (d_249_1368_1781 - 1) in 
  let val fltAppE_1497_1824 = (mixSeed(seed_250_1369_1782 , 4)) in 
  let val fltAppE_1498_1825 = (center_251_1370_1783 + o3_261_1380_1806) in 
  let val c3_269_1388_1826 = (buildOctree(fltAppE_1496_1823 , fltAppE_1497_1824, fltAppE_1498_1825, half__256_1375_1797)) in 
  let val fltAppE_1499_1827 = (d_249_1368_1781 - 1) in 
  let val fltAppE_1500_1828 = (mixSeed(seed_250_1369_1782 , 5)) in 
  let val fltAppE_1501_1829 = (center_251_1370_1783 + stride_257_1376_1799) in 
  let val c4_270_1389_1830 = (buildOctree(fltAppE_1499_1827 , fltAppE_1500_1828, fltAppE_1501_1829, half__256_1375_1797)) in 
  let val fltAppE_1502_1831 = (d_249_1368_1781 - 1) in 
  let val fltAppE_1503_1832 = (mixSeed(seed_250_1369_1782 , 6)) in 
  let val fltAppE_1504_1833 = (center_251_1370_1783 + o5_263_1382_1808) in 
  let val c5_271_1390_1834 = (buildOctree(fltAppE_1502_1831 , fltAppE_1503_1832, fltAppE_1504_1833, half__256_1375_1797)) in 
  let val fltAppE_1505_1835 = (d_249_1368_1781 - 1) in 
  let val fltAppE_1506_1836 = (mixSeed(seed_250_1369_1782 , 7)) in 
  let val fltAppE_1507_1837 = (center_251_1370_1783 + o6_264_1383_1809) in 
  let val c6_272_1391_1838 = (buildOctree(fltAppE_1505_1835 , fltAppE_1506_1836, fltAppE_1507_1837, half__256_1375_1797)) in 
  let val fltAppE_1508_1839 = (d_249_1368_1781 - 1) in 
  let val fltAppE_1509_1840 = (mixSeed(seed_250_1369_1782 , 8)) in 
  let val fltAppE_1510_1841 = (center_251_1370_1783 + o7_265_1384_1810) in 
  let val c7_273_1392_1842 = (buildOctree(fltAppE_1508_1839 , fltAppE_1509_1840, fltAppE_1510_1841, half__256_1375_1797)) in 
  let val m0_274_1393_1843 = (massOf c0_266_1385_1814) in 
  let val m1_275_1394_1844 = (massOf c1_267_1386_1818) in 
  let val m2_276_1395_1845 = (massOf c2_268_1387_1822) in 
  let val m3_277_1396_1846 = (massOf c3_269_1388_1826) in 
  let val m4_278_1397_1847 = (massOf c4_270_1389_1830) in 
  let val m5_279_1398_1848 = (massOf c5_271_1390_1834) in 
  let val m6_280_1399_1849 = (massOf c6_272_1391_1838) in 
  let val m7_281_1400_1850 = (massOf c7_273_1392_1842) in 
  let val mTot_282_1401_1851 = (sum8(m0_274_1393_1843 , m1_275_1394_1844, m2_276_1395_1845, m3_277_1396_1846, m4_278_1397_1847, m5_279_1398_1848, m6_280_1399_1849, m7_281_1400_1850)) in 
  let val fltAppE_1511_1852 = (weightedPos c0_266_1385_1814) in 
  let val fltAppE_1512_1853 = (weightedPos c1_267_1386_1818) in 
  let val fltAppE_1513_1854 = (weightedPos c2_268_1387_1822) in 
  let val fltAppE_1514_1855 = (weightedPos c3_269_1388_1826) in 
  let val fltAppE_1515_1856 = (weightedPos c4_270_1389_1830) in 
  let val fltAppE_1516_1857 = (weightedPos c5_271_1390_1834) in 
  let val fltAppE_1517_1858 = (weightedPos c6_272_1391_1838) in 
  let val fltAppE_1518_1859 = (weightedPos c7_273_1392_1842) in 
  let val wTot_283_1402_1860 = (sum8(fltAppE_1511_1852 , fltAppE_1512_1853, fltAppE_1513_1854, fltAppE_1514_1855, fltAppE_1515_1856, fltAppE_1516_1857, fltAppE_1517_1858, fltAppE_1518_1859)) in 
  let val fltAppE_1519_1861 = (countOf c0_266_1385_1814) in 
  let val fltAppE_1520_1862 = (countOf c1_267_1386_1818) in 
  let val fltAppE_1521_1863 = (countOf c2_268_1387_1822) in 
  let val fltAppE_1522_1864 = (countOf c3_269_1388_1826) in 
  let val fltAppE_1523_1865 = (countOf c4_270_1389_1830) in 
  let val fltAppE_1524_1866 = (countOf c5_271_1390_1834) in 
  let val fltAppE_1525_1867 = (countOf c6_272_1391_1838) in 
  let val fltAppE_1526_1868 = (countOf c7_273_1392_1842) in 
  let val nTot_284_1403_1869 = (sum8(fltAppE_1519_1861 , fltAppE_1520_1862, fltAppE_1521_1863, fltAppE_1522_1864, fltAppE_1523_1865, fltAppE_1524_1866, fltAppE_1525_1867, fltAppE_1526_1868)) in 
  let val fltAppE_1527_1870 = (momentumOf c0_266_1385_1814) in 
  let val fltAppE_1528_1871 = (momentumOf c1_267_1386_1818) in 
  let val fltAppE_1529_1872 = (momentumOf c2_268_1387_1822) in 
  let val fltAppE_1530_1873 = (momentumOf c3_269_1388_1826) in 
  let val fltAppE_1531_1874 = (momentumOf c4_270_1389_1830) in 
  let val fltAppE_1532_1875 = (momentumOf c5_271_1390_1834) in 
  let val fltAppE_1533_1876 = (momentumOf c6_272_1391_1838) in 
  let val fltAppE_1534_1877 = (momentumOf c7_273_1392_1842) in 
  let val pTot_285_1404_1878 = (sum8(fltAppE_1527_1870 , fltAppE_1528_1871, fltAppE_1529_1872, fltAppE_1530_1873, fltAppE_1531_1874, fltAppE_1532_1875, fltAppE_1533_1876, fltAppE_1534_1877)) in 
  let val fltIf_1535_1879 = (mTot_282_1401_1851 = 0) in 
  let val com_286_1405_1880 = 
  (if fltIf_1535_1879 then center_251_1370_1783 
   else (wTot_283_1402_1860 div mTot_282_1401_1851)) in (Cell (mTot_282_1401_1851 , com_286_1405_1880, nTot_284_1403_1869, half_252_1371_1784, pTot_285_1404_1878, c0_266_1385_1814, c1_267_1386_1818, c2_268_1387_1822, c3_269_1388_1826, c4_270_1389_1830, c5_271_1390_1834, c6_272_1391_1838, c7_273_1392_1842)) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end) end;

fun sumEnergy (t_26_1065_1590) = (case t_26_1065_1590 of Cell (m_27_1066_1591 , c_28_1067_1592, wildcard__200_29_1068_1593, s_30_1069_1594, mom_31_1070_1595, a_32_1071_1596, b_33_1072_1597, c1_34_1073_1598, d_35_1074_1599, e_36_1075_1600, f_37_1076_1601, g_38_1077_1602, h_39_1078_1603) => 
  let val fltPrm_1445_1604 = (absI c_28_1067_1592) in 
  let val dist_40_1079_1605 = (fltPrm_1445_1604 + 1) in 
  let val fltPrm_1447_1606 = (m_27_1066_1591 * mom_31_1070_1595) in 
  let val fltPrm_1446_1607 = (fltPrm_1447_1606 * mom_31_1070_1595) in 
  let val fltPrm_1449_1608 = (m_27_1066_1591 * m_27_1066_1591) in 
  let val fltPrm_1448_1609 = (fltPrm_1449_1608 + 1) in 
  let val bulk_41_1080_1610 = (fltPrm_1446_1607 div fltPrm_1448_1609) in 
  let val fltPrm_1451_1611 = (m_27_1066_1591 * s_30_1069_1594) in 
  let val fltPrm_1450_1612 = (fltPrm_1451_1611 * 50) in 
  let val pot_42_1081_1613 = (fltPrm_1450_1612 div dist_40_1079_1605) in 
  let val fltPrm_1452_1614 = (bulk_41_1080_1610 + pot_42_1081_1613) in 
  let val fltAppE_1454_1615 = (sumEnergy a_32_1071_1596) in 
  let val fltAppE_1455_1616 = (sumEnergy b_33_1072_1597) in 
  let val fltAppE_1456_1617 = (sumEnergy c1_34_1073_1598) in 
  let val fltAppE_1457_1618 = (sumEnergy d_35_1074_1599) in 
  let val fltAppE_1458_1619 = (sumEnergy e_36_1075_1600) in 
  let val fltAppE_1459_1620 = (sumEnergy f_37_1076_1601) in 
  let val fltAppE_1460_1621 = (sumEnergy g_38_1077_1602) in 
  let val fltAppE_1461_1622 = (sumEnergy h_39_1078_1603) in 
  let val fltPrm_1453_1623 = (sum8(fltAppE_1454_1615 , fltAppE_1455_1616, fltAppE_1456_1617, fltAppE_1457_1618, fltAppE_1458_1619, fltAppE_1459_1620, fltAppE_1460_1621, fltAppE_1461_1622)) in (fltPrm_1452_1614 + fltPrm_1453_1623) end end end end end end end end end end end end end end end end end end end end 
  | Particle (m_43_1082_1624 , wildcard__217_44_1083_1625, v_45_1084_1626) => 
  let val fltPrm_1463_1627 = (m_43_1082_1624 * v_45_1084_1626) in 
  let val fltPrm_1462_1628 = (fltPrm_1463_1627 * v_45_1084_1626) in (fltPrm_1462_1628 div 2) end end
  | EmptyOct => 0);

fun internal_copy_Octree (arg_902_1032_1557) = (case arg_902_1032_1557 of Cell (x_903_1033_1558 , x_904_1034_1559, x_905_1035_1560, x_906_1036_1561, x_907_1037_1562, x_908_1038_1563, x_909_1039_1564, x_910_1040_1565, x_911_1041_1566, x_912_1042_1567, x_913_1043_1568, x_914_1044_1569, x_915_1045_1570) => 
  let val y_921_1051_1576 = (internal_copy_Octree x_908_1038_1563) in 
  let val y_922_1052_1577 = (internal_copy_Octree x_909_1039_1564) in 
  let val y_923_1053_1578 = (internal_copy_Octree x_910_1040_1565) in 
  let val y_924_1054_1579 = (internal_copy_Octree x_911_1041_1566) in 
  let val y_925_1055_1580 = (internal_copy_Octree x_912_1042_1567) in 
  let val y_926_1056_1581 = (internal_copy_Octree x_913_1043_1568) in 
  let val y_927_1057_1582 = (internal_copy_Octree x_914_1044_1569) in 
  let val y_928_1058_1583 = (internal_copy_Octree x_915_1045_1570) in (Cell (x_903_1033_1558 , x_904_1034_1559, x_905_1035_1560, x_906_1036_1561, x_907_1037_1562, y_921_1051_1576, y_922_1052_1577, y_923_1053_1578, y_924_1054_1579, y_925_1055_1580, y_926_1056_1581, y_927_1057_1582, y_928_1058_1583)) end end end end end end end end 
  | Particle (x_929_1059_1584 , x_930_1060_1585, x_931_1061_1586) => (Particle (x_929_1059_1584 , x_930_1060_1585, x_931_1061_1586))
  | EmptyOct => EmptyOct);
val _ = (print(Int.toString(
  let val wildcard__14_17_1023_1548 = (printsym "Running program OctTree Physics Simulation: ") in 
  let val wildcard__12_18_1024_1549 = (printsym "NEWLINE") in 
  let val octTree_19_1025_1550 = (buildOctree(8 , 17, 0, 64)) in 
  let val wildcard__9_20_1026_1551 = (printsym "Running pass scaleEnergy (map, uses=16): ") in 
  let val wildcard__7_21_1027_1552 = (printsym "NEWLINE") in 
  let val octTree__22_1028_1553 = (scaleEnergy(octTree_19_1025_1550 , 9)) in 
  let val scaledEnergy_23_1029_1554 = (sumEnergy octTree__22_1028_1553) in 
  let val wildcard__2_24_1030_1555 = (printsym "End") in 
  let val wildcard__0_25_1031_1556 = (printsym "NEWLINE") in scaledEnergy_23_1029_1554 end end end end end end end end end)));
val _ = print "\n"
