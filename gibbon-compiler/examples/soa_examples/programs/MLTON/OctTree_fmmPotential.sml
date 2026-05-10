open GibbonCompat;

datatype dat_Octree = Cell of (int  * int * int * int * int *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree) | Particle of (int  * int * int)| EmptyOct ;

fun maxI (a_302_1416_1939 , b_303_1417_1940) = 
  let val fltIf_1548_1941 = (a_302_1416_1939 > b_303_1417_1940) in 
  (if fltIf_1548_1941 then a_302_1416_1939 
   else b_303_1417_1940) end;

fun momentumOf (t_285_1399_1922) = (case t_285_1399_1922 of Cell (wildcard__106_286_1400_1923 , wildcard__107_287_1401_1924, wildcard__108_288_1402_1925, wildcard__109_289_1403_1926, mom_290_1404_1927, wildcard__110_291_1405_1928, wildcard__111_292_1406_1929, wildcard__112_293_1407_1930, wildcard__113_294_1408_1931, wildcard__114_295_1409_1932, wildcard__115_296_1410_1933, wildcard__116_297_1411_1934, wildcard__117_298_1412_1935) => mom_290_1404_1927 
  | Particle (m_299_1413_1936 , wildcard__131_300_1414_1937, v_301_1415_1938) => (m_299_1413_1936 * v_301_1415_1938)
  | EmptyOct => 0);

fun sum8 (a_239_1353_1808 , b_240_1354_1809, c_241_1355_1810, d_242_1356_1811, e_243_1357_1812, f_244_1358_1813, g_245_1359_1814, h_246_1360_1815) = 
  let val fltPrm_1485_1816 = (a_239_1353_1808 + b_240_1354_1809) in 
  let val fltPrm_1484_1817 = (fltPrm_1485_1816 + c_241_1355_1810) in 
  let val fltPrm_1483_1818 = (fltPrm_1484_1817 + d_242_1356_1811) in 
  let val fltPrm_1482_1819 = (fltPrm_1483_1818 + e_243_1357_1812) in 
  let val fltPrm_1481_1820 = (fltPrm_1482_1819 + f_244_1358_1813) in 
  let val fltPrm_1480_1821 = (fltPrm_1481_1820 + g_245_1359_1814) in (fltPrm_1480_1821 + h_246_1360_1815) end end end end end end;

fun absI (x_238_1352_1806) = 
  let val fltIf_1479_1807 = (x_238_1352_1806 < 0) in 
  (if fltIf_1479_1807 then (0 - x_238_1352_1806) 
   else x_238_1352_1806) end;

fun fmmDownSeries (m_230_1344_1790 , mom_231_1345_1791, s_232_1346_1792, dist_233_1347_1793, order_234_1348_1794) = 
  let val fltIf_1471_1795 = (order_234_1348_1794 <= 0) in 
  (if fltIf_1471_1795 then 
  let val fltPrm_1472_1796 = (m_230_1344_1790 * 100) in (fltPrm_1472_1796 div dist_233_1347_1793) end 
   else 
  let val fltAppE_1473_1797 = (order_234_1348_1794 - 1) in 
  let val prev_235_1349_1798 = (fmmDownSeries(m_230_1344_1790 , mom_231_1345_1791, s_232_1346_1792, dist_233_1347_1793, fltAppE_1473_1797)) in 
  let val d_236_1350_1799 = (dist_233_1347_1793 + order_234_1348_1794) in 
  let val fltPrm_1475_1800 = (absI mom_231_1345_1791) in 
  let val fltPrm_1476_1801 = (s_232_1346_1792 * order_234_1348_1794) in 
  let val fltPrm_1474_1802 = (fltPrm_1475_1800 + fltPrm_1476_1801) in 
  let val fltPrm_1478_1803 = (d_236_1350_1799 * d_236_1350_1799) in 
  let val fltPrm_1477_1804 = (fltPrm_1478_1803 + 1) in 
  let val corr_237_1351_1805 = (fltPrm_1474_1802 div fltPrm_1477_1804) in (prev_235_1349_1798 + corr_237_1351_1805) end end end end end end end end end) end;

fun mixSeed (s_228_1342_1785 , salt_229_1343_1786) = 
  let val fltPrm_1469_1787 = (s_228_1342_1785 * 1103) in 
  let val fltPrm_1470_1788 = (salt_229_1343_1786 * 97) in 
  let val fltPrm_1468_1789 = (fltPrm_1469_1787 + fltPrm_1470_1788) in (fltPrm_1468_1789 + 13) end end end;

fun internal_traverse_Octree (arg_929_1229_1708) = (case arg_929_1229_1708 of Cell (x_930_1230_1709 , x_931_1231_1710, x_932_1232_1711, x_933_1233_1712, x_934_1234_1713, x_935_1235_1714, x_936_1236_1715, x_937_1237_1716, x_938_1238_1717, x_939_1239_1718, x_940_1240_1719, x_941_1241_1720, x_942_1242_1721) => 
  let val y_948_1243_1722 = (internal_traverse_Octree x_935_1235_1714) in 
  let val y_949_1244_1723 = (internal_traverse_Octree x_936_1236_1715) in 
  let val y_950_1245_1724 = (internal_traverse_Octree x_937_1237_1716) in 
  let val y_951_1246_1725 = (internal_traverse_Octree x_938_1238_1717) in 
  let val y_952_1247_1726 = (internal_traverse_Octree x_939_1239_1718) in 
  let val y_953_1248_1727 = (internal_traverse_Octree x_940_1240_1719) in 
  let val y_954_1249_1728 = (internal_traverse_Octree x_941_1241_1720) in 
  let val y_955_1250_1729 = (internal_traverse_Octree x_942_1242_1721) in () end end end end end end end end 
  | Particle (x_956_1251_1730 , x_957_1252_1731, x_958_1253_1732) => ()
  | EmptyOct => ());

fun internal_print_Octree (arg_962_1174_1653) = (case arg_962_1174_1653 of Cell (x_963_1175_1654 , x_964_1176_1655, x_965_1177_1656, x_966_1178_1657, x_967_1179_1658, x_968_1180_1659, x_969_1181_1660, x_970_1182_1661, x_971_1183_1662, x_972_1184_1663, x_973_1185_1664, x_974_1186_1665, x_975_1187_1666) => 
  let val wildcard_989_1188_1667 = (print "(Cell") in 
  let val wildcard_1003_1189_1668 = (print " ") in 
  let val y_976_1190_1669 = (print(Int.toString(x_963_1175_1654))) in 
  let val wildcard_1002_1191_1670 = (print " ") in 
  let val y_977_1192_1671 = (print(Int.toString(x_964_1176_1655))) in 
  let val wildcard_1001_1193_1672 = (print " ") in 
  let val y_978_1194_1673 = (print(Int.toString(x_965_1177_1656))) in 
  let val wildcard_1000_1195_1674 = (print " ") in 
  let val y_979_1196_1675 = (print(Int.toString(x_966_1178_1657))) in 
  let val wildcard_999_1197_1676 = (print " ") in 
  let val y_980_1198_1677 = (print(Int.toString(x_967_1179_1658))) in 
  let val wildcard_998_1199_1678 = (print " ") in 
  let val y_981_1200_1679 = (internal_print_Octree x_968_1180_1659) in 
  let val wildcard_997_1201_1680 = (print " ") in 
  let val y_982_1202_1681 = (internal_print_Octree x_969_1181_1660) in 
  let val wildcard_996_1203_1682 = (print " ") in 
  let val y_983_1204_1683 = (internal_print_Octree x_970_1182_1661) in 
  let val wildcard_995_1205_1684 = (print " ") in 
  let val y_984_1206_1685 = (internal_print_Octree x_971_1183_1662) in 
  let val wildcard_994_1207_1686 = (print " ") in 
  let val y_985_1208_1687 = (internal_print_Octree x_972_1184_1663) in 
  let val wildcard_993_1209_1688 = (print " ") in 
  let val y_986_1210_1689 = (internal_print_Octree x_973_1185_1664) in 
  let val wildcard_992_1211_1690 = (print " ") in 
  let val y_987_1212_1691 = (internal_print_Octree x_974_1186_1665) in 
  let val wildcard_991_1213_1692 = (print " ") in 
  let val y_988_1214_1693 = (internal_print_Octree x_975_1187_1666) in 
  let val wildcard_990_1215_1694 = (print ")") in () end end end end end end end end end end end end end end end end end end end end end end end end end end end end 
  | Particle (x_1004_1216_1695 , x_1005_1217_1696, x_1006_1218_1697) => 
  let val wildcard_1010_1219_1698 = (print "(Particle") in 
  let val wildcard_1014_1220_1699 = (print " ") in 
  let val y_1007_1221_1700 = (print(Int.toString(x_1004_1216_1695))) in 
  let val wildcard_1013_1222_1701 = (print " ") in 
  let val y_1008_1223_1702 = (print(Int.toString(x_1005_1217_1696))) in 
  let val wildcard_1012_1224_1703 = (print " ") in 
  let val y_1009_1225_1704 = (print(Int.toString(x_1006_1218_1697))) in 
  let val wildcard_1011_1226_1705 = (print ")") in () end end end end end end end end
  | EmptyOct => 
  let val wildcard_1015_1227_1706 = (print "(EmptyOct") in 
  let val wildcard_1016_1228_1707 = (print ")") in () end end);

fun massOf (t_123_1157_1636) = (case t_123_1157_1636 of Cell (m_124_1158_1637 , wildcard__14_125_1159_1638, wildcard__15_126_1160_1639, wildcard__16_127_1161_1640, wildcard__17_128_1162_1641, wildcard__18_129_1163_1642, wildcard__19_130_1164_1643, wildcard__20_131_1165_1644, wildcard__21_132_1166_1645, wildcard__22_133_1167_1646, wildcard__23_134_1168_1647, wildcard__24_135_1169_1648, wildcard__25_136_1170_1649) => m_124_1158_1637 
  | Particle (m_137_1171_1650 , wildcard__39_138_1172_1651, wildcard__40_139_1173_1652) => m_137_1171_1650
  | EmptyOct => 0);

fun weightedPos (t_106_1140_1619) = (case t_106_1140_1619 of Cell (m_107_1141_1620 , c_108_1142_1621, wildcard__45_109_1143_1622, wildcard__46_110_1144_1623, wildcard__47_111_1145_1624, wildcard__48_112_1146_1625, wildcard__49_113_1147_1626, wildcard__50_114_1148_1627, wildcard__51_115_1149_1628, wildcard__52_116_1150_1629, wildcard__53_117_1151_1630, wildcard__54_118_1152_1631, wildcard__55_119_1153_1632) => (m_107_1141_1620 * c_108_1142_1621) 
  | Particle (m_120_1154_1633 , p_121_1155_1634, wildcard__69_122_1156_1635) => (m_120_1154_1633 * p_121_1155_1634)
  | EmptyOct => 0);

fun fmmUpSeries (m_101_1135_1609 , dip_102_1136_1610, order_103_1137_1611) = 
  let val fltIf_1440_1612 = (order_103_1137_1611 <= 0) in 
  (if fltIf_1440_1612 then (m_101_1135_1609 * 100) 
   else 
  let val fltAppE_1441_1613 = (order_103_1137_1611 - 1) in 
  let val prev_104_1138_1614 = (fmmUpSeries(m_101_1135_1609 , dip_102_1136_1610, fltAppE_1441_1613)) in 
  let val fltPrm_1442_1615 = (absI dip_102_1136_1610) in 
  let val fltPrm_1444_1616 = (order_103_1137_1611 * 20) in 
  let val fltPrm_1443_1617 = (fltPrm_1444_1616 + 1) in 
  let val corr_105_1139_1618 = (fltPrm_1442_1615 div fltPrm_1443_1617) in (prev_104_1138_1614 + corr_105_1139_1618) end end end end end end) end;

fun fmmPotential (t_157_1271_1733 , probe_158_1272_1734, order_159_1273_1735, eta_160_1274_1736) = (case t_157_1271_1733 of Cell (m_161_1275_1737 , c_162_1276_1738, wildcard__319_163_1277_1739, s_164_1278_1740, mom_165_1279_1741, a_166_1280_1742, b_167_1281_1743, c1_168_1282_1744, d_169_1283_1745, e_170_1284_1746, f_171_1285_1747, g_172_1286_1748, h_173_1287_1749) => 
  let val fltAppE_1446_1750 = (c_162_1276_1738 - probe_158_1272_1734) in 
  let val fltPrm_1445_1751 = (absI fltAppE_1446_1750) in 
  let val dist_174_1288_1752 = (fltPrm_1445_1751 + 1) in 
  let val farLhs_175_1289_1753 = (s_164_1278_1740 * 100) in 
  let val farRhs_176_1290_1754 = (eta_160_1274_1736 * dist_174_1288_1752) in 
  let val fltAppE_1447_1755 = (m_161_1275_1737 * c_162_1276_1738) in 
  let val upMoment_177_1291_1756 = (fmmUpSeries(m_161_1275_1737 , fltAppE_1447_1755, order_159_1273_1735)) in 
  let val downApprox_178_1292_1757 = (fmmDownSeries(m_161_1275_1737 , mom_165_1279_1741, s_164_1278_1740, dist_174_1288_1752, order_159_1273_1735)) in 
  let val fltPrm_1449_1758 = (dist_174_1288_1752 + 1) in 
  let val fltPrm_1448_1759 = (upMoment_177_1291_1756 div fltPrm_1449_1758) in 
  let val approx_179_1293_1760 = (fltPrm_1448_1759 + downApprox_178_1292_1757) in 
  let val fltAppE_1450_1761 = (fmmPotential(a_166_1280_1742 , probe_158_1272_1734, order_159_1273_1735, eta_160_1274_1736)) in 
  let val fltAppE_1451_1762 = (fmmPotential(b_167_1281_1743 , probe_158_1272_1734, order_159_1273_1735, eta_160_1274_1736)) in 
  let val fltAppE_1452_1763 = (fmmPotential(c1_168_1282_1744 , probe_158_1272_1734, order_159_1273_1735, eta_160_1274_1736)) in 
  let val fltAppE_1453_1764 = (fmmPotential(d_169_1283_1745 , probe_158_1272_1734, order_159_1273_1735, eta_160_1274_1736)) in 
  let val fltAppE_1454_1765 = (fmmPotential(e_170_1284_1746 , probe_158_1272_1734, order_159_1273_1735, eta_160_1274_1736)) in 
  let val fltAppE_1455_1766 = (fmmPotential(f_171_1285_1747 , probe_158_1272_1734, order_159_1273_1735, eta_160_1274_1736)) in 
  let val fltAppE_1456_1767 = (fmmPotential(g_172_1286_1748 , probe_158_1272_1734, order_159_1273_1735, eta_160_1274_1736)) in 
  let val fltAppE_1457_1768 = (fmmPotential(h_173_1287_1749 , probe_158_1272_1734, order_159_1273_1735, eta_160_1274_1736)) in 
  let val recur_180_1294_1769 = (sum8(fltAppE_1450_1761 , fltAppE_1451_1762, fltAppE_1452_1763, fltAppE_1453_1764, fltAppE_1454_1765, fltAppE_1455_1766, fltAppE_1456_1767, fltAppE_1457_1768)) in 
  let val fltIf_1458_1770 = (farLhs_175_1289_1753 < farRhs_176_1290_1754) in 
  (if fltIf_1458_1770 then approx_179_1293_1760 
   else recur_180_1294_1769) end end end end end end end end end end end end end end end end end end end end end 
  | Particle (m_181_1295_1771 , p_182_1296_1772, v_183_1297_1773) => 
  let val fltAppE_1460_1774 = (p_182_1296_1772 - probe_158_1272_1734) in 
  let val fltPrm_1459_1775 = (absI fltAppE_1460_1774) in 
  let val dist_184_1298_1776 = (fltPrm_1459_1775 + 1) in 
  let val fltAppE_1461_1777 = (m_181_1295_1771 * p_182_1296_1772) in 
  let val up_185_1299_1778 = (fmmUpSeries(m_181_1295_1771 , fltAppE_1461_1777, order_159_1273_1735)) in 
  let val fltPrm_1463_1779 = (dist_184_1298_1776 + 1) in 
  let val fltPrm_1462_1780 = (up_185_1299_1778 div fltPrm_1463_1779) in 
  let val fltPrm_1466_1781 = (m_181_1295_1771 * 100) in 
  let val fltPrm_1467_1782 = (absI v_183_1297_1773) in 
  let val fltPrm_1465_1783 = (fltPrm_1466_1781 + fltPrm_1467_1782) in 
  let val fltPrm_1464_1784 = (fltPrm_1465_1783 div dist_184_1298_1776) in (fltPrm_1462_1780 + fltPrm_1464_1784) end end end end end end end end end end end
  | EmptyOct => 0);

fun countOf (t_44_1078_1592) = (case t_44_1078_1592 of Cell (wildcard__74_45_1079_1593 , wildcard__75_46_1080_1594, n_47_1081_1595, wildcard__76_48_1082_1596, wildcard__77_49_1083_1597, wildcard__78_50_1084_1598, wildcard__79_51_1085_1599, wildcard__80_52_1086_1600, wildcard__81_53_1087_1601, wildcard__82_54_1088_1602, wildcard__83_55_1089_1603, wildcard__84_56_1090_1604, wildcard__85_57_1091_1605) => n_47_1081_1595 
  | Particle (wildcard__99_58_1092_1606 , wildcard__100_59_1093_1607, wildcard__101_60_1094_1608) => 1
  | EmptyOct => 0);

fun buildOctree (d_247_1361_1822 , seed_248_1362_1823, center_249_1363_1824, half_250_1364_1825) = 
  let val fltIf_1486_1826 = (d_247_1361_1822 = 0) in 
  (if fltIf_1486_1826 then 
  let val fltPrm_1488_1827 = (absI seed_248_1362_1823) in 
  let val fltPrm_1487_1828 = (fltPrm_1488_1827 mod 5) in 
  let val m_251_1365_1829 = (1 + fltPrm_1487_1828) in 
  let val fltPrm_1491_1830 = (mixSeed(seed_248_1362_1823 , 3)) in 
  let val fltPrm_1490_1831 = (fltPrm_1491_1830 mod 3) in 
  let val fltPrm_1489_1832 = (center_249_1363_1824 + fltPrm_1490_1831) in 
  let val p_252_1366_1833 = (fltPrm_1489_1832 - 1) in 
  let val fltPrm_1493_1834 = (mixSeed(seed_248_1362_1823 , 11)) in 
  let val fltPrm_1492_1835 = (fltPrm_1493_1834 mod 11) in 
  let val v_253_1367_1836 = (fltPrm_1492_1835 - 5) in (Particle (m_251_1365_1829 , p_252_1366_1833, v_253_1367_1836)) end end end end end end end end end end 
   else 
  let val fltAppE_1494_1837 = (half_250_1364_1825 div 2) in 
  let val half__254_1368_1838 = (maxI(1 , fltAppE_1494_1837)) in 
  let val fltAppE_1495_1839 = (half_250_1364_1825 div 4) in 
  let val stride_255_1369_1840 = (maxI(1 , fltAppE_1495_1839)) in 
  let val fltPrm_1496_1841 = (stride_255_1369_1840 * 7) in 
  let val o0_256_1370_1842 = (0 - fltPrm_1496_1841) in 
  let val fltPrm_1497_1843 = (stride_255_1369_1840 * 5) in 
  let val o1_257_1371_1844 = (0 - fltPrm_1497_1843) in 
  let val fltPrm_1498_1845 = (stride_255_1369_1840 * 3) in 
  let val o2_258_1372_1846 = (0 - fltPrm_1498_1845) in 
  let val o3_259_1373_1847 = (0 - stride_255_1369_1840) in 
  let val o5_261_1375_1849 = (stride_255_1369_1840 * 3) in 
  let val o6_262_1376_1850 = (stride_255_1369_1840 * 5) in 
  let val o7_263_1377_1851 = (stride_255_1369_1840 * 7) in 
  let val fltAppE_1499_1852 = (d_247_1361_1822 - 1) in 
  let val fltAppE_1500_1853 = (mixSeed(seed_248_1362_1823 , 1)) in 
  let val fltAppE_1501_1854 = (center_249_1363_1824 + o0_256_1370_1842) in 
  let val c0_264_1378_1855 = (buildOctree(fltAppE_1499_1852 , fltAppE_1500_1853, fltAppE_1501_1854, half__254_1368_1838)) in 
  let val fltAppE_1502_1856 = (d_247_1361_1822 - 1) in 
  let val fltAppE_1503_1857 = (mixSeed(seed_248_1362_1823 , 2)) in 
  let val fltAppE_1504_1858 = (center_249_1363_1824 + o1_257_1371_1844) in 
  let val c1_265_1379_1859 = (buildOctree(fltAppE_1502_1856 , fltAppE_1503_1857, fltAppE_1504_1858, half__254_1368_1838)) in 
  let val fltAppE_1505_1860 = (d_247_1361_1822 - 1) in 
  let val fltAppE_1506_1861 = (mixSeed(seed_248_1362_1823 , 3)) in 
  let val fltAppE_1507_1862 = (center_249_1363_1824 + o2_258_1372_1846) in 
  let val c2_266_1380_1863 = (buildOctree(fltAppE_1505_1860 , fltAppE_1506_1861, fltAppE_1507_1862, half__254_1368_1838)) in 
  let val fltAppE_1508_1864 = (d_247_1361_1822 - 1) in 
  let val fltAppE_1509_1865 = (mixSeed(seed_248_1362_1823 , 4)) in 
  let val fltAppE_1510_1866 = (center_249_1363_1824 + o3_259_1373_1847) in 
  let val c3_267_1381_1867 = (buildOctree(fltAppE_1508_1864 , fltAppE_1509_1865, fltAppE_1510_1866, half__254_1368_1838)) in 
  let val fltAppE_1511_1868 = (d_247_1361_1822 - 1) in 
  let val fltAppE_1512_1869 = (mixSeed(seed_248_1362_1823 , 5)) in 
  let val fltAppE_1513_1870 = (center_249_1363_1824 + stride_255_1369_1840) in 
  let val c4_268_1382_1871 = (buildOctree(fltAppE_1511_1868 , fltAppE_1512_1869, fltAppE_1513_1870, half__254_1368_1838)) in 
  let val fltAppE_1514_1872 = (d_247_1361_1822 - 1) in 
  let val fltAppE_1515_1873 = (mixSeed(seed_248_1362_1823 , 6)) in 
  let val fltAppE_1516_1874 = (center_249_1363_1824 + o5_261_1375_1849) in 
  let val c5_269_1383_1875 = (buildOctree(fltAppE_1514_1872 , fltAppE_1515_1873, fltAppE_1516_1874, half__254_1368_1838)) in 
  let val fltAppE_1517_1876 = (d_247_1361_1822 - 1) in 
  let val fltAppE_1518_1877 = (mixSeed(seed_248_1362_1823 , 7)) in 
  let val fltAppE_1519_1878 = (center_249_1363_1824 + o6_262_1376_1850) in 
  let val c6_270_1384_1879 = (buildOctree(fltAppE_1517_1876 , fltAppE_1518_1877, fltAppE_1519_1878, half__254_1368_1838)) in 
  let val fltAppE_1520_1880 = (d_247_1361_1822 - 1) in 
  let val fltAppE_1521_1881 = (mixSeed(seed_248_1362_1823 , 8)) in 
  let val fltAppE_1522_1882 = (center_249_1363_1824 + o7_263_1377_1851) in 
  let val c7_271_1385_1883 = (buildOctree(fltAppE_1520_1880 , fltAppE_1521_1881, fltAppE_1522_1882, half__254_1368_1838)) in 
  let val m0_272_1386_1884 = (massOf c0_264_1378_1855) in 
  let val m1_273_1387_1885 = (massOf c1_265_1379_1859) in 
  let val m2_274_1388_1886 = (massOf c2_266_1380_1863) in 
  let val m3_275_1389_1887 = (massOf c3_267_1381_1867) in 
  let val m4_276_1390_1888 = (massOf c4_268_1382_1871) in 
  let val m5_277_1391_1889 = (massOf c5_269_1383_1875) in 
  let val m6_278_1392_1890 = (massOf c6_270_1384_1879) in 
  let val m7_279_1393_1891 = (massOf c7_271_1385_1883) in 
  let val mTot_280_1394_1892 = (sum8(m0_272_1386_1884 , m1_273_1387_1885, m2_274_1388_1886, m3_275_1389_1887, m4_276_1390_1888, m5_277_1391_1889, m6_278_1392_1890, m7_279_1393_1891)) in 
  let val fltAppE_1523_1893 = (weightedPos c0_264_1378_1855) in 
  let val fltAppE_1524_1894 = (weightedPos c1_265_1379_1859) in 
  let val fltAppE_1525_1895 = (weightedPos c2_266_1380_1863) in 
  let val fltAppE_1526_1896 = (weightedPos c3_267_1381_1867) in 
  let val fltAppE_1527_1897 = (weightedPos c4_268_1382_1871) in 
  let val fltAppE_1528_1898 = (weightedPos c5_269_1383_1875) in 
  let val fltAppE_1529_1899 = (weightedPos c6_270_1384_1879) in 
  let val fltAppE_1530_1900 = (weightedPos c7_271_1385_1883) in 
  let val wTot_281_1395_1901 = (sum8(fltAppE_1523_1893 , fltAppE_1524_1894, fltAppE_1525_1895, fltAppE_1526_1896, fltAppE_1527_1897, fltAppE_1528_1898, fltAppE_1529_1899, fltAppE_1530_1900)) in 
  let val fltAppE_1531_1902 = (countOf c0_264_1378_1855) in 
  let val fltAppE_1532_1903 = (countOf c1_265_1379_1859) in 
  let val fltAppE_1533_1904 = (countOf c2_266_1380_1863) in 
  let val fltAppE_1534_1905 = (countOf c3_267_1381_1867) in 
  let val fltAppE_1535_1906 = (countOf c4_268_1382_1871) in 
  let val fltAppE_1536_1907 = (countOf c5_269_1383_1875) in 
  let val fltAppE_1537_1908 = (countOf c6_270_1384_1879) in 
  let val fltAppE_1538_1909 = (countOf c7_271_1385_1883) in 
  let val nTot_282_1396_1910 = (sum8(fltAppE_1531_1902 , fltAppE_1532_1903, fltAppE_1533_1904, fltAppE_1534_1905, fltAppE_1535_1906, fltAppE_1536_1907, fltAppE_1537_1908, fltAppE_1538_1909)) in 
  let val fltAppE_1539_1911 = (momentumOf c0_264_1378_1855) in 
  let val fltAppE_1540_1912 = (momentumOf c1_265_1379_1859) in 
  let val fltAppE_1541_1913 = (momentumOf c2_266_1380_1863) in 
  let val fltAppE_1542_1914 = (momentumOf c3_267_1381_1867) in 
  let val fltAppE_1543_1915 = (momentumOf c4_268_1382_1871) in 
  let val fltAppE_1544_1916 = (momentumOf c5_269_1383_1875) in 
  let val fltAppE_1545_1917 = (momentumOf c6_270_1384_1879) in 
  let val fltAppE_1546_1918 = (momentumOf c7_271_1385_1883) in 
  let val pTot_283_1397_1919 = (sum8(fltAppE_1539_1911 , fltAppE_1540_1912, fltAppE_1541_1913, fltAppE_1542_1914, fltAppE_1543_1915, fltAppE_1544_1916, fltAppE_1545_1917, fltAppE_1546_1918)) in 
  let val fltIf_1547_1920 = (mTot_280_1394_1892 = 0) in 
  let val com_284_1398_1921 = 
  (if fltIf_1547_1920 then center_249_1363_1824 
   else (wTot_281_1395_1901 div mTot_280_1394_1892)) in (Cell (mTot_280_1394_1892 , com_284_1398_1921, nTot_282_1396_1910, half_250_1364_1825, pTot_283_1397_1919, c0_264_1378_1855, c1_265_1379_1859, c2_266_1380_1863, c3_267_1381_1867, c4_268_1382_1871, c5_269_1383_1875, c6_270_1384_1879, c7_271_1385_1883)) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end) end;

fun internal_copy_Octree (arg_896_1025_1559) = (case arg_896_1025_1559 of Cell (x_897_1026_1560 , x_898_1027_1561, x_899_1028_1562, x_900_1029_1563, x_901_1030_1564, x_902_1031_1565, x_903_1032_1566, x_904_1033_1567, x_905_1034_1568, x_906_1035_1569, x_907_1036_1570, x_908_1037_1571, x_909_1038_1572) => 
  let val y_915_1044_1578 = (internal_copy_Octree x_902_1031_1565) in 
  let val y_916_1045_1579 = (internal_copy_Octree x_903_1032_1566) in 
  let val y_917_1046_1580 = (internal_copy_Octree x_904_1033_1567) in 
  let val y_918_1047_1581 = (internal_copy_Octree x_905_1034_1568) in 
  let val y_919_1048_1582 = (internal_copy_Octree x_906_1035_1569) in 
  let val y_920_1049_1583 = (internal_copy_Octree x_907_1036_1570) in 
  let val y_921_1050_1584 = (internal_copy_Octree x_908_1037_1571) in 
  let val y_922_1051_1585 = (internal_copy_Octree x_909_1038_1572) in (Cell (x_897_1026_1560 , x_898_1027_1561, x_899_1028_1562, x_900_1029_1563, x_901_1030_1564, y_915_1044_1578, y_916_1045_1579, y_917_1046_1580, y_918_1047_1581, y_919_1048_1582, y_920_1049_1583, y_921_1050_1584, y_922_1051_1585)) end end end end end end end end 
  | Particle (x_923_1052_1586 , x_924_1053_1587, x_925_1054_1588) => (Particle (x_923_1052_1586 , x_924_1053_1587, x_925_1054_1588))
  | EmptyOct => EmptyOct);
val _ = (print(Int.toString(
  let val wildcard__13_16_1017_1549 = (printsym "Running program OctTree Physics Simulation: ") in 
  let val wildcard__11_17_1018_1550 = (printsym "NEWLINE") in 
  let val fltPrm_1439_1551 = 1 in 
  let val fltAppE_1438_1552 = (fltPrm_1439_1551 + 8) in 
  let val octTree_18_1019_1553 = (buildOctree(fltAppE_1438_1552 , 17, 0, 64)) in 
  let val wildcard__8_19_1020_1554 = (printsym "Running pass fmmPotential (fold_like, uses=12): ") in 
  let val wildcard__6_20_1021_1555 = (printsym "NEWLINE") in 
  let val fmmPot_21_1022_1556 = (fmmPotential(octTree_18_1019_1553 , 21, 4, 70)) in 
  let val wildcard__2_22_1023_1557 = (printsym "End") in 
  let val wildcard__0_23_1024_1558 = (printsym "NEWLINE") in fmmPot_21_1022_1556 end end end end end end end end end end)));
val _ = print "\n"
