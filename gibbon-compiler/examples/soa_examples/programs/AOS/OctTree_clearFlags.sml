datatype dat_Octree = Cell of (int  * int * int * int * int *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree) | Particle of (int  * int * int)| EmptyOct ;

fun maxI (a_304_1423_1909 , b_305_1424_1910) = 
  let val fltIf_1537_1911 = (a_304_1423_1909 > b_305_1424_1910) in 
  (if fltIf_1537_1911 then a_304_1423_1909 
   else b_305_1424_1910) end;

fun momentumOf (t_287_1406_1892) = (case t_287_1406_1892 of Cell (wildcard__106_288_1407_1893 , wildcard__107_289_1408_1894, wildcard__108_290_1409_1895, wildcard__109_291_1410_1896, mom_292_1411_1897, wildcard__110_293_1412_1898, wildcard__111_294_1413_1899, wildcard__112_295_1414_1900, wildcard__113_296_1415_1901, wildcard__114_297_1416_1902, wildcard__115_298_1417_1903, wildcard__116_299_1418_1904, wildcard__117_300_1419_1905) => mom_292_1411_1897 
  | Particle (m_301_1420_1906 , wildcard__131_302_1421_1907, v_303_1422_1908) => (m_301_1420_1906 * v_303_1422_1908)
  | EmptyOct => 0);

fun sum8 (a_241_1360_1778 , b_242_1361_1779, c_243_1362_1780, d_244_1363_1781, e_245_1364_1782, f_246_1365_1783, g_247_1366_1784, h_248_1367_1785) = 
  let val fltPrm_1474_1786 = (a_241_1360_1778 + b_242_1361_1779) in 
  let val fltPrm_1473_1787 = (fltPrm_1474_1786 + c_243_1362_1780) in 
  let val fltPrm_1472_1788 = (fltPrm_1473_1787 + d_244_1363_1781) in 
  let val fltPrm_1471_1789 = (fltPrm_1472_1788 + e_245_1364_1782) in 
  let val fltPrm_1470_1790 = (fltPrm_1471_1789 + f_246_1365_1783) in 
  let val fltPrm_1469_1791 = (fltPrm_1470_1790 + g_247_1366_1784) in (fltPrm_1469_1791 + h_248_1367_1785) end end end end end end;

fun absI (x_240_1359_1776) = 
  let val fltIf_1468_1777 = (x_240_1359_1776 < 0) in 
  (if fltIf_1468_1777 then (0 - x_240_1359_1776) 
   else x_240_1359_1776) end;

fun mixSeed (s_230_1349_1771 , salt_231_1350_1772) = 
  let val fltPrm_1466_1773 = (s_230_1349_1771 * 1103) in 
  let val fltPrm_1467_1774 = (salt_231_1350_1772 * 97) in 
  let val fltPrm_1465_1775 = (fltPrm_1466_1773 + fltPrm_1467_1774) in (fltPrm_1465_1775 + 13) end end end;

fun clearFlags (t_142_1261_1746) = (case t_142_1261_1746 of Cell (m_143_1262_1747 , c_144_1263_1748, wildcard__369_145_1264_1749, s_146_1265_1750, mom_147_1266_1751, a_148_1267_1752, b_149_1268_1753, c1_150_1269_1754, d_151_1270_1755, e_152_1271_1756, f_153_1272_1757, g_154_1273_1758, h_155_1274_1759) => 
  let val fltPkd_1457_1760 = (clearFlags a_148_1267_1752) in 
  let val fltPkd_1458_1761 = (clearFlags b_149_1268_1753) in 
  let val fltPkd_1459_1762 = (clearFlags c1_150_1269_1754) in 
  let val fltPkd_1460_1763 = (clearFlags d_151_1270_1755) in 
  let val fltPkd_1461_1764 = (clearFlags e_152_1271_1756) in 
  let val fltPkd_1462_1765 = (clearFlags f_153_1272_1757) in 
  let val fltPkd_1463_1766 = (clearFlags g_154_1273_1758) in 
  let val fltPkd_1464_1767 = (clearFlags h_155_1274_1759) in (Cell (m_143_1262_1747 , c_144_1263_1748, 0, s_146_1265_1750, mom_147_1266_1751, fltPkd_1457_1760, fltPkd_1458_1761, fltPkd_1459_1762, fltPkd_1460_1763, fltPkd_1461_1764, fltPkd_1462_1765, fltPkd_1463_1766, fltPkd_1464_1767)) end end end end end end end end 
  | Particle (m_156_1275_1768 , p_157_1276_1769, v_158_1277_1770) => (Particle (m_156_1275_1768 , p_157_1276_1769, v_158_1277_1770))
  | EmptyOct => EmptyOct);

fun internal_traverse_Octree (arg_935_1236_1721) = (case arg_935_1236_1721 of Cell (x_936_1237_1722 , x_937_1238_1723, x_938_1239_1724, x_939_1240_1725, x_940_1241_1726, x_941_1242_1727, x_942_1243_1728, x_943_1244_1729, x_944_1245_1730, x_945_1246_1731, x_946_1247_1732, x_947_1248_1733, x_948_1249_1734) => 
  let val y_954_1250_1735 = (internal_traverse_Octree x_941_1242_1727) in 
  let val y_955_1251_1736 = (internal_traverse_Octree x_942_1243_1728) in 
  let val y_956_1252_1737 = (internal_traverse_Octree x_943_1244_1729) in 
  let val y_957_1253_1738 = (internal_traverse_Octree x_944_1245_1730) in 
  let val y_958_1254_1739 = (internal_traverse_Octree x_945_1246_1731) in 
  let val y_959_1255_1740 = (internal_traverse_Octree x_946_1247_1732) in 
  let val y_960_1256_1741 = (internal_traverse_Octree x_947_1248_1733) in 
  let val y_961_1257_1742 = (internal_traverse_Octree x_948_1249_1734) in () end end end end end end end end 
  | Particle (x_962_1258_1743 , x_963_1259_1744, x_964_1260_1745) => ()
  | EmptyOct => ());

fun internal_print_Octree (arg_968_1181_1666) = (case arg_968_1181_1666 of Cell (x_969_1182_1667 , x_970_1183_1668, x_971_1184_1669, x_972_1185_1670, x_973_1186_1671, x_974_1187_1672, x_975_1188_1673, x_976_1189_1674, x_977_1190_1675, x_978_1191_1676, x_979_1192_1677, x_980_1193_1678, x_981_1194_1679) => 
  let val wildcard_995_1195_1680 = (print "(Cell") in 
  let val wildcard_1009_1196_1681 = (print " ") in 
  let val y_982_1197_1682 = (print(Int.toString(x_969_1182_1667))) in 
  let val wildcard_1008_1198_1683 = (print " ") in 
  let val y_983_1199_1684 = (print(Int.toString(x_970_1183_1668))) in 
  let val wildcard_1007_1200_1685 = (print " ") in 
  let val y_984_1201_1686 = (print(Int.toString(x_971_1184_1669))) in 
  let val wildcard_1006_1202_1687 = (print " ") in 
  let val y_985_1203_1688 = (print(Int.toString(x_972_1185_1670))) in 
  let val wildcard_1005_1204_1689 = (print " ") in 
  let val y_986_1205_1690 = (print(Int.toString(x_973_1186_1671))) in 
  let val wildcard_1004_1206_1691 = (print " ") in 
  let val y_987_1207_1692 = (internal_print_Octree x_974_1187_1672) in 
  let val wildcard_1003_1208_1693 = (print " ") in 
  let val y_988_1209_1694 = (internal_print_Octree x_975_1188_1673) in 
  let val wildcard_1002_1210_1695 = (print " ") in 
  let val y_989_1211_1696 = (internal_print_Octree x_976_1189_1674) in 
  let val wildcard_1001_1212_1697 = (print " ") in 
  let val y_990_1213_1698 = (internal_print_Octree x_977_1190_1675) in 
  let val wildcard_1000_1214_1699 = (print " ") in 
  let val y_991_1215_1700 = (internal_print_Octree x_978_1191_1676) in 
  let val wildcard_999_1216_1701 = (print " ") in 
  let val y_992_1217_1702 = (internal_print_Octree x_979_1192_1677) in 
  let val wildcard_998_1218_1703 = (print " ") in 
  let val y_993_1219_1704 = (internal_print_Octree x_980_1193_1678) in 
  let val wildcard_997_1220_1705 = (print " ") in 
  let val y_994_1221_1706 = (internal_print_Octree x_981_1194_1679) in 
  let val wildcard_996_1222_1707 = (print ")") in () end end end end end end end end end end end end end end end end end end end end end end end end end end end end 
  | Particle (x_1010_1223_1708 , x_1011_1224_1709, x_1012_1225_1710) => 
  let val wildcard_1016_1226_1711 = (print "(Particle") in 
  let val wildcard_1020_1227_1712 = (print " ") in 
  let val y_1013_1228_1713 = (print(Int.toString(x_1010_1223_1708))) in 
  let val wildcard_1019_1229_1714 = (print " ") in 
  let val y_1014_1230_1715 = (print(Int.toString(x_1011_1224_1709))) in 
  let val wildcard_1018_1231_1716 = (print " ") in 
  let val y_1015_1232_1717 = (print(Int.toString(x_1012_1225_1710))) in 
  let val wildcard_1017_1233_1718 = (print ")") in () end end end end end end end end
  | EmptyOct => 
  let val wildcard_1021_1234_1719 = (print "(EmptyOct") in 
  let val wildcard_1022_1235_1720 = (print ")") in () end end);

fun massOf (t_125_1164_1649) = (case t_125_1164_1649 of Cell (m_126_1165_1650 , wildcard__14_127_1166_1651, wildcard__15_128_1167_1652, wildcard__16_129_1168_1653, wildcard__17_130_1169_1654, wildcard__18_131_1170_1655, wildcard__19_132_1171_1656, wildcard__20_133_1172_1657, wildcard__21_134_1173_1658, wildcard__22_135_1174_1659, wildcard__23_136_1175_1660, wildcard__24_137_1176_1661, wildcard__25_138_1177_1662) => m_126_1165_1650 
  | Particle (m_139_1178_1663 , wildcard__39_140_1179_1664, wildcard__40_141_1180_1665) => m_139_1178_1663
  | EmptyOct => 0);

fun weightedPos (t_108_1147_1632) = (case t_108_1147_1632 of Cell (m_109_1148_1633 , c_110_1149_1634, wildcard__45_111_1150_1635, wildcard__46_112_1151_1636, wildcard__47_113_1152_1637, wildcard__48_114_1153_1638, wildcard__49_115_1154_1639, wildcard__50_116_1155_1640, wildcard__51_117_1156_1641, wildcard__52_118_1157_1642, wildcard__53_119_1158_1643, wildcard__54_120_1159_1644, wildcard__55_121_1160_1645) => (m_109_1148_1633 * c_110_1149_1634) 
  | Particle (m_122_1161_1646 , p_123_1162_1647, wildcard__69_124_1163_1648) => (m_122_1161_1646 * p_123_1162_1647)
  | EmptyOct => 0);

fun countActive (t_80_1119_1597 , theta_81_1120_1598) = (case t_80_1119_1597 of Cell (wildcard__223_82_1121_1599 , c_83_1122_1600, wildcard__224_84_1123_1601, s_85_1124_1602, wildcard__225_86_1125_1603, a_87_1126_1604, b_88_1127_1605, c1_89_1128_1606, d_90_1129_1607, e_91_1130_1608, f_92_1131_1609, g_93_1132_1610, h_94_1133_1611) => 
  let val fltAppE_1446_1613 = (c_83_1122_1600 - 0) in 
  let val fltPrm_1445_1614 = (absI fltAppE_1446_1613) in 
  let val dist_96_1135_1615 = (fltPrm_1445_1614 + 1) in 
  let val openLhs_97_1136_1616 = (s_85_1124_1602 * 100) in 
  let val openRhs_98_1137_1617 = (theta_81_1120_1598 * dist_96_1135_1615) in 
  let val fltIf_1447_1618 = (openLhs_97_1136_1616 >= openRhs_98_1137_1617) in 
  let val refine_99_1138_1619 = 
  (if fltIf_1447_1618 then 1 
   else 0) in 
  let val fltAppE_1449_1620 = (countActive(a_87_1126_1604 , theta_81_1120_1598)) in 
  let val fltAppE_1450_1621 = (countActive(b_88_1127_1605 , theta_81_1120_1598)) in 
  let val fltAppE_1451_1622 = (countActive(c1_89_1128_1606 , theta_81_1120_1598)) in 
  let val fltAppE_1452_1623 = (countActive(d_90_1129_1607 , theta_81_1120_1598)) in 
  let val fltAppE_1453_1624 = (countActive(e_91_1130_1608 , theta_81_1120_1598)) in 
  let val fltAppE_1454_1625 = (countActive(f_92_1131_1609 , theta_81_1120_1598)) in 
  let val fltAppE_1455_1626 = (countActive(g_93_1132_1610 , theta_81_1120_1598)) in 
  let val fltAppE_1456_1627 = (countActive(h_94_1133_1611 , theta_81_1120_1598)) in 
  let val fltPrm_1448_1628 = (sum8(fltAppE_1449_1620 , fltAppE_1450_1621, fltAppE_1451_1622, fltAppE_1452_1623, fltAppE_1453_1624, fltAppE_1454_1625, fltAppE_1455_1626, fltAppE_1456_1627)) in (refine_99_1138_1619 + fltPrm_1448_1628) end end end end end end end end end end end end end end end end 
  | Particle (wildcard__244_100_1139_1629 , wildcard__245_101_1140_1630, wildcard__246_102_1141_1631) => 0
  | EmptyOct => 0);

fun countOf (t_46_1085_1580) = (case t_46_1085_1580 of Cell (wildcard__74_47_1086_1581 , wildcard__75_48_1087_1582, n_49_1088_1583, wildcard__76_50_1089_1584, wildcard__77_51_1090_1585, wildcard__78_52_1091_1586, wildcard__79_53_1092_1587, wildcard__80_54_1093_1588, wildcard__81_55_1094_1589, wildcard__82_56_1095_1590, wildcard__83_57_1096_1591, wildcard__84_58_1097_1592, wildcard__85_59_1098_1593) => n_49_1088_1583 
  | Particle (wildcard__99_60_1099_1594 , wildcard__100_61_1100_1595, wildcard__101_62_1101_1596) => 1
  | EmptyOct => 0);

fun buildOctree (d_249_1368_1792 , seed_250_1369_1793, center_251_1370_1794, half_252_1371_1795) = 
  let val fltIf_1475_1796 = (d_249_1368_1792 = 0) in 
  (if fltIf_1475_1796 then 
  let val fltPrm_1477_1797 = (absI seed_250_1369_1793) in 
  let val fltPrm_1476_1798 = (fltPrm_1477_1797 mod 5) in 
  let val m_253_1372_1799 = (1 + fltPrm_1476_1798) in 
  let val fltPrm_1480_1800 = (mixSeed(seed_250_1369_1793 , 3)) in 
  let val fltPrm_1479_1801 = (fltPrm_1480_1800 mod 3) in 
  let val fltPrm_1478_1802 = (center_251_1370_1794 + fltPrm_1479_1801) in 
  let val p_254_1373_1803 = (fltPrm_1478_1802 - 1) in 
  let val fltPrm_1482_1804 = (mixSeed(seed_250_1369_1793 , 11)) in 
  let val fltPrm_1481_1805 = (fltPrm_1482_1804 mod 11) in 
  let val v_255_1374_1806 = (fltPrm_1481_1805 - 5) in (Particle (m_253_1372_1799 , p_254_1373_1803, v_255_1374_1806)) end end end end end end end end end end 
   else 
  let val fltAppE_1483_1807 = (half_252_1371_1795 div 2) in 
  let val half__256_1375_1808 = (maxI(1 , fltAppE_1483_1807)) in 
  let val fltAppE_1484_1809 = (half_252_1371_1795 div 4) in 
  let val stride_257_1376_1810 = (maxI(1 , fltAppE_1484_1809)) in 
  let val fltPrm_1485_1811 = (stride_257_1376_1810 * 7) in 
  let val o0_258_1377_1812 = (0 - fltPrm_1485_1811) in 
  let val fltPrm_1486_1813 = (stride_257_1376_1810 * 5) in 
  let val o1_259_1378_1814 = (0 - fltPrm_1486_1813) in 
  let val fltPrm_1487_1815 = (stride_257_1376_1810 * 3) in 
  let val o2_260_1379_1816 = (0 - fltPrm_1487_1815) in 
  let val o3_261_1380_1817 = (0 - stride_257_1376_1810) in 
  let val o5_263_1382_1819 = (stride_257_1376_1810 * 3) in 
  let val o6_264_1383_1820 = (stride_257_1376_1810 * 5) in 
  let val o7_265_1384_1821 = (stride_257_1376_1810 * 7) in 
  let val fltAppE_1488_1822 = (d_249_1368_1792 - 1) in 
  let val fltAppE_1489_1823 = (mixSeed(seed_250_1369_1793 , 1)) in 
  let val fltAppE_1490_1824 = (center_251_1370_1794 + o0_258_1377_1812) in 
  let val c0_266_1385_1825 = (buildOctree(fltAppE_1488_1822 , fltAppE_1489_1823, fltAppE_1490_1824, half__256_1375_1808)) in 
  let val fltAppE_1491_1826 = (d_249_1368_1792 - 1) in 
  let val fltAppE_1492_1827 = (mixSeed(seed_250_1369_1793 , 2)) in 
  let val fltAppE_1493_1828 = (center_251_1370_1794 + o1_259_1378_1814) in 
  let val c1_267_1386_1829 = (buildOctree(fltAppE_1491_1826 , fltAppE_1492_1827, fltAppE_1493_1828, half__256_1375_1808)) in 
  let val fltAppE_1494_1830 = (d_249_1368_1792 - 1) in 
  let val fltAppE_1495_1831 = (mixSeed(seed_250_1369_1793 , 3)) in 
  let val fltAppE_1496_1832 = (center_251_1370_1794 + o2_260_1379_1816) in 
  let val c2_268_1387_1833 = (buildOctree(fltAppE_1494_1830 , fltAppE_1495_1831, fltAppE_1496_1832, half__256_1375_1808)) in 
  let val fltAppE_1497_1834 = (d_249_1368_1792 - 1) in 
  let val fltAppE_1498_1835 = (mixSeed(seed_250_1369_1793 , 4)) in 
  let val fltAppE_1499_1836 = (center_251_1370_1794 + o3_261_1380_1817) in 
  let val c3_269_1388_1837 = (buildOctree(fltAppE_1497_1834 , fltAppE_1498_1835, fltAppE_1499_1836, half__256_1375_1808)) in 
  let val fltAppE_1500_1838 = (d_249_1368_1792 - 1) in 
  let val fltAppE_1501_1839 = (mixSeed(seed_250_1369_1793 , 5)) in 
  let val fltAppE_1502_1840 = (center_251_1370_1794 + stride_257_1376_1810) in 
  let val c4_270_1389_1841 = (buildOctree(fltAppE_1500_1838 , fltAppE_1501_1839, fltAppE_1502_1840, half__256_1375_1808)) in 
  let val fltAppE_1503_1842 = (d_249_1368_1792 - 1) in 
  let val fltAppE_1504_1843 = (mixSeed(seed_250_1369_1793 , 6)) in 
  let val fltAppE_1505_1844 = (center_251_1370_1794 + o5_263_1382_1819) in 
  let val c5_271_1390_1845 = (buildOctree(fltAppE_1503_1842 , fltAppE_1504_1843, fltAppE_1505_1844, half__256_1375_1808)) in 
  let val fltAppE_1506_1846 = (d_249_1368_1792 - 1) in 
  let val fltAppE_1507_1847 = (mixSeed(seed_250_1369_1793 , 7)) in 
  let val fltAppE_1508_1848 = (center_251_1370_1794 + o6_264_1383_1820) in 
  let val c6_272_1391_1849 = (buildOctree(fltAppE_1506_1846 , fltAppE_1507_1847, fltAppE_1508_1848, half__256_1375_1808)) in 
  let val fltAppE_1509_1850 = (d_249_1368_1792 - 1) in 
  let val fltAppE_1510_1851 = (mixSeed(seed_250_1369_1793 , 8)) in 
  let val fltAppE_1511_1852 = (center_251_1370_1794 + o7_265_1384_1821) in 
  let val c7_273_1392_1853 = (buildOctree(fltAppE_1509_1850 , fltAppE_1510_1851, fltAppE_1511_1852, half__256_1375_1808)) in 
  let val m0_274_1393_1854 = (massOf c0_266_1385_1825) in 
  let val m1_275_1394_1855 = (massOf c1_267_1386_1829) in 
  let val m2_276_1395_1856 = (massOf c2_268_1387_1833) in 
  let val m3_277_1396_1857 = (massOf c3_269_1388_1837) in 
  let val m4_278_1397_1858 = (massOf c4_270_1389_1841) in 
  let val m5_279_1398_1859 = (massOf c5_271_1390_1845) in 
  let val m6_280_1399_1860 = (massOf c6_272_1391_1849) in 
  let val m7_281_1400_1861 = (massOf c7_273_1392_1853) in 
  let val mTot_282_1401_1862 = (sum8(m0_274_1393_1854 , m1_275_1394_1855, m2_276_1395_1856, m3_277_1396_1857, m4_278_1397_1858, m5_279_1398_1859, m6_280_1399_1860, m7_281_1400_1861)) in 
  let val fltAppE_1512_1863 = (weightedPos c0_266_1385_1825) in 
  let val fltAppE_1513_1864 = (weightedPos c1_267_1386_1829) in 
  let val fltAppE_1514_1865 = (weightedPos c2_268_1387_1833) in 
  let val fltAppE_1515_1866 = (weightedPos c3_269_1388_1837) in 
  let val fltAppE_1516_1867 = (weightedPos c4_270_1389_1841) in 
  let val fltAppE_1517_1868 = (weightedPos c5_271_1390_1845) in 
  let val fltAppE_1518_1869 = (weightedPos c6_272_1391_1849) in 
  let val fltAppE_1519_1870 = (weightedPos c7_273_1392_1853) in 
  let val wTot_283_1402_1871 = (sum8(fltAppE_1512_1863 , fltAppE_1513_1864, fltAppE_1514_1865, fltAppE_1515_1866, fltAppE_1516_1867, fltAppE_1517_1868, fltAppE_1518_1869, fltAppE_1519_1870)) in 
  let val fltAppE_1520_1872 = (countOf c0_266_1385_1825) in 
  let val fltAppE_1521_1873 = (countOf c1_267_1386_1829) in 
  let val fltAppE_1522_1874 = (countOf c2_268_1387_1833) in 
  let val fltAppE_1523_1875 = (countOf c3_269_1388_1837) in 
  let val fltAppE_1524_1876 = (countOf c4_270_1389_1841) in 
  let val fltAppE_1525_1877 = (countOf c5_271_1390_1845) in 
  let val fltAppE_1526_1878 = (countOf c6_272_1391_1849) in 
  let val fltAppE_1527_1879 = (countOf c7_273_1392_1853) in 
  let val nTot_284_1403_1880 = (sum8(fltAppE_1520_1872 , fltAppE_1521_1873, fltAppE_1522_1874, fltAppE_1523_1875, fltAppE_1524_1876, fltAppE_1525_1877, fltAppE_1526_1878, fltAppE_1527_1879)) in 
  let val fltAppE_1528_1881 = (momentumOf c0_266_1385_1825) in 
  let val fltAppE_1529_1882 = (momentumOf c1_267_1386_1829) in 
  let val fltAppE_1530_1883 = (momentumOf c2_268_1387_1833) in 
  let val fltAppE_1531_1884 = (momentumOf c3_269_1388_1837) in 
  let val fltAppE_1532_1885 = (momentumOf c4_270_1389_1841) in 
  let val fltAppE_1533_1886 = (momentumOf c5_271_1390_1845) in 
  let val fltAppE_1534_1887 = (momentumOf c6_272_1391_1849) in 
  let val fltAppE_1535_1888 = (momentumOf c7_273_1392_1853) in 
  let val pTot_285_1404_1889 = (sum8(fltAppE_1528_1881 , fltAppE_1529_1882, fltAppE_1530_1883, fltAppE_1531_1884, fltAppE_1532_1885, fltAppE_1533_1886, fltAppE_1534_1887, fltAppE_1535_1888)) in 
  let val fltIf_1536_1890 = (mTot_282_1401_1862 = 0) in 
  let val com_286_1405_1891 = 
  (if fltIf_1536_1890 then center_251_1370_1794 
   else (wTot_283_1402_1871 div mTot_282_1401_1862)) in (Cell (mTot_282_1401_1862 , com_286_1405_1891, nTot_284_1403_1880, half_252_1371_1795, pTot_285_1404_1889, c0_266_1385_1825, c1_267_1386_1829, c2_268_1387_1833, c3_269_1388_1837, c4_270_1389_1841, c5_271_1390_1845, c6_272_1391_1849, c7_273_1392_1853)) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end) end;

fun internal_copy_Octree (arg_902_1032_1547) = (case arg_902_1032_1547 of Cell (x_903_1033_1548 , x_904_1034_1549, x_905_1035_1550, x_906_1036_1551, x_907_1037_1552, x_908_1038_1553, x_909_1039_1554, x_910_1040_1555, x_911_1041_1556, x_912_1042_1557, x_913_1043_1558, x_914_1044_1559, x_915_1045_1560) => 
  let val y_921_1051_1566 = (internal_copy_Octree x_908_1038_1553) in 
  let val y_922_1052_1567 = (internal_copy_Octree x_909_1039_1554) in 
  let val y_923_1053_1568 = (internal_copy_Octree x_910_1040_1555) in 
  let val y_924_1054_1569 = (internal_copy_Octree x_911_1041_1556) in 
  let val y_925_1055_1570 = (internal_copy_Octree x_912_1042_1557) in 
  let val y_926_1056_1571 = (internal_copy_Octree x_913_1043_1558) in 
  let val y_927_1057_1572 = (internal_copy_Octree x_914_1044_1559) in 
  let val y_928_1058_1573 = (internal_copy_Octree x_915_1045_1560) in (Cell (x_903_1033_1548 , x_904_1034_1549, x_905_1035_1550, x_906_1036_1551, x_907_1037_1552, y_921_1051_1566, y_922_1052_1567, y_923_1053_1568, y_924_1054_1569, y_925_1055_1570, y_926_1056_1571, y_927_1057_1572, y_928_1058_1573)) end end end end end end end end 
  | Particle (x_929_1059_1574 , x_930_1060_1575, x_931_1061_1576) => (Particle (x_929_1059_1574 , x_930_1060_1575, x_931_1061_1576))
  | EmptyOct => EmptyOct);
val _ = (print(Int.toString(
  let val wildcard__14_17_1023_1538 = (print "Running program OctTree Physics Simulation: ") in 
  let val wildcard__12_18_1024_1539 = (print "NEWLINE") in 
  let val octTree_19_1025_1540 = (buildOctree(8 , 17, 0, 64)) in 
  let val wildcard__9_20_1026_1541 = (print "Running pass clearFlags (map, uses=15): ") in 
  let val wildcard__7_21_1027_1542 = (print "NEWLINE") in 
  let val octTree___22_1028_1543 = (clearFlags octTree_19_1025_1540) in 
  let val active_23_1029_1544 = (countActive(octTree___22_1028_1543 , 60)) in 
  let val wildcard__2_24_1030_1545 = (print "End") in 
  let val wildcard__0_25_1031_1546 = (print "NEWLINE") in active_23_1029_1544 end end end end end end end end end)));
val _ = print "\n"
