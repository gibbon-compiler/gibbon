open GibbonCompat;

datatype dat_Octree = Cell of (int  * int * int * int * int *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree) | Particle of (int  * int * int)| EmptyOct ;

fun maxI (a_302_1416_1883 , b_303_1417_1884) = 
  let val fltIf_1531_1885 = (a_302_1416_1883 > b_303_1417_1884) in 
  (if fltIf_1531_1885 then a_302_1416_1883 
   else b_303_1417_1884) end;

fun momentumOf (t_285_1399_1866) = (case t_285_1399_1866 of Cell (wildcard__106_286_1400_1867 , wildcard__107_287_1401_1868, wildcard__108_288_1402_1869, wildcard__109_289_1403_1870, mom_290_1404_1871, wildcard__110_291_1405_1872, wildcard__111_292_1406_1873, wildcard__112_293_1407_1874, wildcard__113_294_1408_1875, wildcard__114_295_1409_1876, wildcard__115_296_1410_1877, wildcard__116_297_1411_1878, wildcard__117_298_1412_1879) => mom_290_1404_1871 
  | Particle (m_299_1413_1880 , wildcard__131_300_1414_1881, v_301_1415_1882) => (m_299_1413_1880 * v_301_1415_1882)
  | EmptyOct => 0);

fun sum8 (a_239_1353_1752 , b_240_1354_1753, c_241_1355_1754, d_242_1356_1755, e_243_1357_1756, f_244_1358_1757, g_245_1359_1758, h_246_1360_1759) = 
  let val fltPrm_1468_1760 = (a_239_1353_1752 + b_240_1354_1753) in 
  let val fltPrm_1467_1761 = (fltPrm_1468_1760 + c_241_1355_1754) in 
  let val fltPrm_1466_1762 = (fltPrm_1467_1761 + d_242_1356_1755) in 
  let val fltPrm_1465_1763 = (fltPrm_1466_1762 + e_243_1357_1756) in 
  let val fltPrm_1464_1764 = (fltPrm_1465_1763 + f_244_1358_1757) in 
  let val fltPrm_1463_1765 = (fltPrm_1464_1764 + g_245_1359_1758) in (fltPrm_1463_1765 + h_246_1360_1759) end end end end end end;

fun absI (x_238_1352_1750) = 
  let val fltIf_1462_1751 = (x_238_1352_1750 < 0) in 
  (if fltIf_1462_1751 then (0 - x_238_1352_1750) 
   else x_238_1352_1750) end;

fun mixSeed (s_228_1342_1745 , salt_229_1343_1746) = 
  let val fltPrm_1460_1747 = (s_228_1342_1745 * 1103) in 
  let val fltPrm_1461_1748 = (salt_229_1343_1746 * 97) in 
  let val fltPrm_1459_1749 = (fltPrm_1460_1747 + fltPrm_1461_1748) in (fltPrm_1459_1749 + 13) end end end;

fun internal_traverse_Octree (arg_929_1229_1720) = (case arg_929_1229_1720 of Cell (x_930_1230_1721 , x_931_1231_1722, x_932_1232_1723, x_933_1233_1724, x_934_1234_1725, x_935_1235_1726, x_936_1236_1727, x_937_1237_1728, x_938_1238_1729, x_939_1239_1730, x_940_1240_1731, x_941_1241_1732, x_942_1242_1733) => 
  let val y_948_1243_1734 = (internal_traverse_Octree x_935_1235_1726) in 
  let val y_949_1244_1735 = (internal_traverse_Octree x_936_1236_1727) in 
  let val y_950_1245_1736 = (internal_traverse_Octree x_937_1237_1728) in 
  let val y_951_1246_1737 = (internal_traverse_Octree x_938_1238_1729) in 
  let val y_952_1247_1738 = (internal_traverse_Octree x_939_1239_1730) in 
  let val y_953_1248_1739 = (internal_traverse_Octree x_940_1240_1731) in 
  let val y_954_1249_1740 = (internal_traverse_Octree x_941_1241_1732) in 
  let val y_955_1250_1741 = (internal_traverse_Octree x_942_1242_1733) in () end end end end end end end end 
  | Particle (x_956_1251_1742 , x_957_1252_1743, x_958_1253_1744) => ()
  | EmptyOct => ());

fun internal_print_Octree (arg_962_1174_1665) = (case arg_962_1174_1665 of Cell (x_963_1175_1666 , x_964_1176_1667, x_965_1177_1668, x_966_1178_1669, x_967_1179_1670, x_968_1180_1671, x_969_1181_1672, x_970_1182_1673, x_971_1183_1674, x_972_1184_1675, x_973_1185_1676, x_974_1186_1677, x_975_1187_1678) => 
  let val wildcard_989_1188_1679 = (print "(Cell") in 
  let val wildcard_1003_1189_1680 = (print " ") in 
  let val y_976_1190_1681 = (print(Int.toString(x_963_1175_1666))) in 
  let val wildcard_1002_1191_1682 = (print " ") in 
  let val y_977_1192_1683 = (print(Int.toString(x_964_1176_1667))) in 
  let val wildcard_1001_1193_1684 = (print " ") in 
  let val y_978_1194_1685 = (print(Int.toString(x_965_1177_1668))) in 
  let val wildcard_1000_1195_1686 = (print " ") in 
  let val y_979_1196_1687 = (print(Int.toString(x_966_1178_1669))) in 
  let val wildcard_999_1197_1688 = (print " ") in 
  let val y_980_1198_1689 = (print(Int.toString(x_967_1179_1670))) in 
  let val wildcard_998_1199_1690 = (print " ") in 
  let val y_981_1200_1691 = (internal_print_Octree x_968_1180_1671) in 
  let val wildcard_997_1201_1692 = (print " ") in 
  let val y_982_1202_1693 = (internal_print_Octree x_969_1181_1672) in 
  let val wildcard_996_1203_1694 = (print " ") in 
  let val y_983_1204_1695 = (internal_print_Octree x_970_1182_1673) in 
  let val wildcard_995_1205_1696 = (print " ") in 
  let val y_984_1206_1697 = (internal_print_Octree x_971_1183_1674) in 
  let val wildcard_994_1207_1698 = (print " ") in 
  let val y_985_1208_1699 = (internal_print_Octree x_972_1184_1675) in 
  let val wildcard_993_1209_1700 = (print " ") in 
  let val y_986_1210_1701 = (internal_print_Octree x_973_1185_1676) in 
  let val wildcard_992_1211_1702 = (print " ") in 
  let val y_987_1212_1703 = (internal_print_Octree x_974_1186_1677) in 
  let val wildcard_991_1213_1704 = (print " ") in 
  let val y_988_1214_1705 = (internal_print_Octree x_975_1187_1678) in 
  let val wildcard_990_1215_1706 = (print ")") in () end end end end end end end end end end end end end end end end end end end end end end end end end end end end 
  | Particle (x_1004_1216_1707 , x_1005_1217_1708, x_1006_1218_1709) => 
  let val wildcard_1010_1219_1710 = (print "(Particle") in 
  let val wildcard_1014_1220_1711 = (print " ") in 
  let val y_1007_1221_1712 = (print(Int.toString(x_1004_1216_1707))) in 
  let val wildcard_1013_1222_1713 = (print " ") in 
  let val y_1008_1223_1714 = (print(Int.toString(x_1005_1217_1708))) in 
  let val wildcard_1012_1224_1715 = (print " ") in 
  let val y_1009_1225_1716 = (print(Int.toString(x_1006_1218_1709))) in 
  let val wildcard_1011_1226_1717 = (print ")") in () end end end end end end end end
  | EmptyOct => 
  let val wildcard_1015_1227_1718 = (print "(EmptyOct") in 
  let val wildcard_1016_1228_1719 = (print ")") in () end end);

fun massOf (t_123_1157_1648) = (case t_123_1157_1648 of Cell (m_124_1158_1649 , wildcard__14_125_1159_1650, wildcard__15_126_1160_1651, wildcard__16_127_1161_1652, wildcard__17_128_1162_1653, wildcard__18_129_1163_1654, wildcard__19_130_1164_1655, wildcard__20_131_1165_1656, wildcard__21_132_1166_1657, wildcard__22_133_1167_1658, wildcard__23_134_1168_1659, wildcard__24_135_1169_1660, wildcard__25_136_1170_1661) => m_124_1158_1649 
  | Particle (m_137_1171_1662 , wildcard__39_138_1172_1663, wildcard__40_139_1173_1664) => m_137_1171_1662
  | EmptyOct => 0);

fun weightedPos (t_106_1140_1631) = (case t_106_1140_1631 of Cell (m_107_1141_1632 , c_108_1142_1633, wildcard__45_109_1143_1634, wildcard__46_110_1144_1635, wildcard__47_111_1145_1636, wildcard__48_112_1146_1637, wildcard__49_113_1147_1638, wildcard__50_114_1148_1639, wildcard__51_115_1149_1640, wildcard__52_116_1150_1641, wildcard__53_117_1151_1642, wildcard__54_118_1152_1643, wildcard__55_119_1153_1644) => (m_107_1141_1632 * c_108_1142_1633) 
  | Particle (m_120_1154_1645 , p_121_1155_1646, wildcard__69_122_1156_1647) => (m_120_1154_1645 * p_121_1155_1646)
  | EmptyOct => 0);

fun countOf (t_44_1078_1614) = (case t_44_1078_1614 of Cell (wildcard__74_45_1079_1615 , wildcard__75_46_1080_1616, n_47_1081_1617, wildcard__76_48_1082_1618, wildcard__77_49_1083_1619, wildcard__78_50_1084_1620, wildcard__79_51_1085_1621, wildcard__80_52_1086_1622, wildcard__81_53_1087_1623, wildcard__82_54_1088_1624, wildcard__83_55_1089_1625, wildcard__84_56_1090_1626, wildcard__85_57_1091_1627) => n_47_1081_1617 
  | Particle (wildcard__99_58_1092_1628 , wildcard__100_59_1093_1629, wildcard__101_60_1094_1630) => 1
  | EmptyOct => 0);

fun buildOctree (d_247_1361_1766 , seed_248_1362_1767, center_249_1363_1768, half_250_1364_1769) = 
  let val fltIf_1469_1770 = (d_247_1361_1766 = 0) in 
  (if fltIf_1469_1770 then 
  let val fltPrm_1471_1771 = (absI seed_248_1362_1767) in 
  let val fltPrm_1470_1772 = (fltPrm_1471_1771 mod 5) in 
  let val m_251_1365_1773 = (1 + fltPrm_1470_1772) in 
  let val fltPrm_1474_1774 = (mixSeed(seed_248_1362_1767 , 3)) in 
  let val fltPrm_1473_1775 = (fltPrm_1474_1774 mod 3) in 
  let val fltPrm_1472_1776 = (center_249_1363_1768 + fltPrm_1473_1775) in 
  let val p_252_1366_1777 = (fltPrm_1472_1776 - 1) in 
  let val fltPrm_1476_1778 = (mixSeed(seed_248_1362_1767 , 11)) in 
  let val fltPrm_1475_1779 = (fltPrm_1476_1778 mod 11) in 
  let val v_253_1367_1780 = (fltPrm_1475_1779 - 5) in (Particle (m_251_1365_1773 , p_252_1366_1777, v_253_1367_1780)) end end end end end end end end end end 
   else 
  let val fltAppE_1477_1781 = (half_250_1364_1769 div 2) in 
  let val half__254_1368_1782 = (maxI(1 , fltAppE_1477_1781)) in 
  let val fltAppE_1478_1783 = (half_250_1364_1769 div 4) in 
  let val stride_255_1369_1784 = (maxI(1 , fltAppE_1478_1783)) in 
  let val fltPrm_1479_1785 = (stride_255_1369_1784 * 7) in 
  let val o0_256_1370_1786 = (0 - fltPrm_1479_1785) in 
  let val fltPrm_1480_1787 = (stride_255_1369_1784 * 5) in 
  let val o1_257_1371_1788 = (0 - fltPrm_1480_1787) in 
  let val fltPrm_1481_1789 = (stride_255_1369_1784 * 3) in 
  let val o2_258_1372_1790 = (0 - fltPrm_1481_1789) in 
  let val o3_259_1373_1791 = (0 - stride_255_1369_1784) in 
  let val o5_261_1375_1793 = (stride_255_1369_1784 * 3) in 
  let val o6_262_1376_1794 = (stride_255_1369_1784 * 5) in 
  let val o7_263_1377_1795 = (stride_255_1369_1784 * 7) in 
  let val fltAppE_1482_1796 = (d_247_1361_1766 - 1) in 
  let val fltAppE_1483_1797 = (mixSeed(seed_248_1362_1767 , 1)) in 
  let val fltAppE_1484_1798 = (center_249_1363_1768 + o0_256_1370_1786) in 
  let val c0_264_1378_1799 = (buildOctree(fltAppE_1482_1796 , fltAppE_1483_1797, fltAppE_1484_1798, half__254_1368_1782)) in 
  let val fltAppE_1485_1800 = (d_247_1361_1766 - 1) in 
  let val fltAppE_1486_1801 = (mixSeed(seed_248_1362_1767 , 2)) in 
  let val fltAppE_1487_1802 = (center_249_1363_1768 + o1_257_1371_1788) in 
  let val c1_265_1379_1803 = (buildOctree(fltAppE_1485_1800 , fltAppE_1486_1801, fltAppE_1487_1802, half__254_1368_1782)) in 
  let val fltAppE_1488_1804 = (d_247_1361_1766 - 1) in 
  let val fltAppE_1489_1805 = (mixSeed(seed_248_1362_1767 , 3)) in 
  let val fltAppE_1490_1806 = (center_249_1363_1768 + o2_258_1372_1790) in 
  let val c2_266_1380_1807 = (buildOctree(fltAppE_1488_1804 , fltAppE_1489_1805, fltAppE_1490_1806, half__254_1368_1782)) in 
  let val fltAppE_1491_1808 = (d_247_1361_1766 - 1) in 
  let val fltAppE_1492_1809 = (mixSeed(seed_248_1362_1767 , 4)) in 
  let val fltAppE_1493_1810 = (center_249_1363_1768 + o3_259_1373_1791) in 
  let val c3_267_1381_1811 = (buildOctree(fltAppE_1491_1808 , fltAppE_1492_1809, fltAppE_1493_1810, half__254_1368_1782)) in 
  let val fltAppE_1494_1812 = (d_247_1361_1766 - 1) in 
  let val fltAppE_1495_1813 = (mixSeed(seed_248_1362_1767 , 5)) in 
  let val fltAppE_1496_1814 = (center_249_1363_1768 + stride_255_1369_1784) in 
  let val c4_268_1382_1815 = (buildOctree(fltAppE_1494_1812 , fltAppE_1495_1813, fltAppE_1496_1814, half__254_1368_1782)) in 
  let val fltAppE_1497_1816 = (d_247_1361_1766 - 1) in 
  let val fltAppE_1498_1817 = (mixSeed(seed_248_1362_1767 , 6)) in 
  let val fltAppE_1499_1818 = (center_249_1363_1768 + o5_261_1375_1793) in 
  let val c5_269_1383_1819 = (buildOctree(fltAppE_1497_1816 , fltAppE_1498_1817, fltAppE_1499_1818, half__254_1368_1782)) in 
  let val fltAppE_1500_1820 = (d_247_1361_1766 - 1) in 
  let val fltAppE_1501_1821 = (mixSeed(seed_248_1362_1767 , 7)) in 
  let val fltAppE_1502_1822 = (center_249_1363_1768 + o6_262_1376_1794) in 
  let val c6_270_1384_1823 = (buildOctree(fltAppE_1500_1820 , fltAppE_1501_1821, fltAppE_1502_1822, half__254_1368_1782)) in 
  let val fltAppE_1503_1824 = (d_247_1361_1766 - 1) in 
  let val fltAppE_1504_1825 = (mixSeed(seed_248_1362_1767 , 8)) in 
  let val fltAppE_1505_1826 = (center_249_1363_1768 + o7_263_1377_1795) in 
  let val c7_271_1385_1827 = (buildOctree(fltAppE_1503_1824 , fltAppE_1504_1825, fltAppE_1505_1826, half__254_1368_1782)) in 
  let val m0_272_1386_1828 = (massOf c0_264_1378_1799) in 
  let val m1_273_1387_1829 = (massOf c1_265_1379_1803) in 
  let val m2_274_1388_1830 = (massOf c2_266_1380_1807) in 
  let val m3_275_1389_1831 = (massOf c3_267_1381_1811) in 
  let val m4_276_1390_1832 = (massOf c4_268_1382_1815) in 
  let val m5_277_1391_1833 = (massOf c5_269_1383_1819) in 
  let val m6_278_1392_1834 = (massOf c6_270_1384_1823) in 
  let val m7_279_1393_1835 = (massOf c7_271_1385_1827) in 
  let val mTot_280_1394_1836 = (sum8(m0_272_1386_1828 , m1_273_1387_1829, m2_274_1388_1830, m3_275_1389_1831, m4_276_1390_1832, m5_277_1391_1833, m6_278_1392_1834, m7_279_1393_1835)) in 
  let val fltAppE_1506_1837 = (weightedPos c0_264_1378_1799) in 
  let val fltAppE_1507_1838 = (weightedPos c1_265_1379_1803) in 
  let val fltAppE_1508_1839 = (weightedPos c2_266_1380_1807) in 
  let val fltAppE_1509_1840 = (weightedPos c3_267_1381_1811) in 
  let val fltAppE_1510_1841 = (weightedPos c4_268_1382_1815) in 
  let val fltAppE_1511_1842 = (weightedPos c5_269_1383_1819) in 
  let val fltAppE_1512_1843 = (weightedPos c6_270_1384_1823) in 
  let val fltAppE_1513_1844 = (weightedPos c7_271_1385_1827) in 
  let val wTot_281_1395_1845 = (sum8(fltAppE_1506_1837 , fltAppE_1507_1838, fltAppE_1508_1839, fltAppE_1509_1840, fltAppE_1510_1841, fltAppE_1511_1842, fltAppE_1512_1843, fltAppE_1513_1844)) in 
  let val fltAppE_1514_1846 = (countOf c0_264_1378_1799) in 
  let val fltAppE_1515_1847 = (countOf c1_265_1379_1803) in 
  let val fltAppE_1516_1848 = (countOf c2_266_1380_1807) in 
  let val fltAppE_1517_1849 = (countOf c3_267_1381_1811) in 
  let val fltAppE_1518_1850 = (countOf c4_268_1382_1815) in 
  let val fltAppE_1519_1851 = (countOf c5_269_1383_1819) in 
  let val fltAppE_1520_1852 = (countOf c6_270_1384_1823) in 
  let val fltAppE_1521_1853 = (countOf c7_271_1385_1827) in 
  let val nTot_282_1396_1854 = (sum8(fltAppE_1514_1846 , fltAppE_1515_1847, fltAppE_1516_1848, fltAppE_1517_1849, fltAppE_1518_1850, fltAppE_1519_1851, fltAppE_1520_1852, fltAppE_1521_1853)) in 
  let val fltAppE_1522_1855 = (momentumOf c0_264_1378_1799) in 
  let val fltAppE_1523_1856 = (momentumOf c1_265_1379_1803) in 
  let val fltAppE_1524_1857 = (momentumOf c2_266_1380_1807) in 
  let val fltAppE_1525_1858 = (momentumOf c3_267_1381_1811) in 
  let val fltAppE_1526_1859 = (momentumOf c4_268_1382_1815) in 
  let val fltAppE_1527_1860 = (momentumOf c5_269_1383_1819) in 
  let val fltAppE_1528_1861 = (momentumOf c6_270_1384_1823) in 
  let val fltAppE_1529_1862 = (momentumOf c7_271_1385_1827) in 
  let val pTot_283_1397_1863 = (sum8(fltAppE_1522_1855 , fltAppE_1523_1856, fltAppE_1524_1857, fltAppE_1525_1858, fltAppE_1526_1859, fltAppE_1527_1860, fltAppE_1528_1861, fltAppE_1529_1862)) in 
  let val fltIf_1530_1864 = (mTot_280_1394_1836 = 0) in 
  let val com_284_1398_1865 = 
  (if fltIf_1530_1864 then center_249_1363_1768 
   else (wTot_281_1395_1845 div mTot_280_1394_1836)) in (Cell (mTot_280_1394_1836 , com_284_1398_1865, nTot_282_1396_1854, half_250_1364_1769, pTot_283_1397_1863, c0_264_1378_1799, c1_265_1379_1803, c2_266_1380_1807, c3_267_1381_1811, c4_268_1382_1815, c5_269_1383_1819, c6_270_1384_1823, c7_271_1385_1827)) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end) end;

fun sumEnergy (t_24_1058_1575) = (case t_24_1058_1575 of Cell (m_25_1059_1576 , c_26_1060_1577, wildcard__200_27_1061_1578, s_28_1062_1579, mom_29_1063_1580, a_30_1064_1581, b_31_1065_1582, c1_32_1066_1583, d_33_1067_1584, e_34_1068_1585, f_35_1069_1586, g_36_1070_1587, h_37_1071_1588) => 
  let val fltPrm_1440_1589 = (absI c_26_1060_1577) in 
  let val dist_38_1072_1590 = (fltPrm_1440_1589 + 1) in 
  let val fltPrm_1442_1591 = (m_25_1059_1576 * mom_29_1063_1580) in 
  let val fltPrm_1441_1592 = (fltPrm_1442_1591 * mom_29_1063_1580) in 
  let val fltPrm_1444_1593 = (m_25_1059_1576 * m_25_1059_1576) in 
  let val fltPrm_1443_1594 = (fltPrm_1444_1593 + 1) in 
  let val bulk_39_1073_1595 = (fltPrm_1441_1592 div fltPrm_1443_1594) in 
  let val fltPrm_1446_1596 = (m_25_1059_1576 * s_28_1062_1579) in 
  let val fltPrm_1445_1597 = (fltPrm_1446_1596 * 50) in 
  let val pot_40_1074_1598 = (fltPrm_1445_1597 div dist_38_1072_1590) in 
  let val fltPrm_1447_1599 = (bulk_39_1073_1595 + pot_40_1074_1598) in 
  let val fltAppE_1449_1600 = (sumEnergy a_30_1064_1581) in 
  let val fltAppE_1450_1601 = (sumEnergy b_31_1065_1582) in 
  let val fltAppE_1451_1602 = (sumEnergy c1_32_1066_1583) in 
  let val fltAppE_1452_1603 = (sumEnergy d_33_1067_1584) in 
  let val fltAppE_1453_1604 = (sumEnergy e_34_1068_1585) in 
  let val fltAppE_1454_1605 = (sumEnergy f_35_1069_1586) in 
  let val fltAppE_1455_1606 = (sumEnergy g_36_1070_1587) in 
  let val fltAppE_1456_1607 = (sumEnergy h_37_1071_1588) in 
  let val fltPrm_1448_1608 = (sum8(fltAppE_1449_1600 , fltAppE_1450_1601, fltAppE_1451_1602, fltAppE_1452_1603, fltAppE_1453_1604, fltAppE_1454_1605, fltAppE_1455_1606, fltAppE_1456_1607)) in (fltPrm_1447_1599 + fltPrm_1448_1608) end end end end end end end end end end end end end end end end end end end end 
  | Particle (m_41_1075_1609 , wildcard__217_42_1076_1610, v_43_1077_1611) => 
  let val fltPrm_1458_1612 = (m_41_1075_1609 * v_43_1077_1611) in 
  let val fltPrm_1457_1613 = (fltPrm_1458_1612 * v_43_1077_1611) in (fltPrm_1457_1613 div 2) end end
  | EmptyOct => 0);

fun internal_copy_Octree (arg_896_1025_1542) = (case arg_896_1025_1542 of Cell (x_897_1026_1543 , x_898_1027_1544, x_899_1028_1545, x_900_1029_1546, x_901_1030_1547, x_902_1031_1548, x_903_1032_1549, x_904_1033_1550, x_905_1034_1551, x_906_1035_1552, x_907_1036_1553, x_908_1037_1554, x_909_1038_1555) => 
  let val y_915_1044_1561 = (internal_copy_Octree x_902_1031_1548) in 
  let val y_916_1045_1562 = (internal_copy_Octree x_903_1032_1549) in 
  let val y_917_1046_1563 = (internal_copy_Octree x_904_1033_1550) in 
  let val y_918_1047_1564 = (internal_copy_Octree x_905_1034_1551) in 
  let val y_919_1048_1565 = (internal_copy_Octree x_906_1035_1552) in 
  let val y_920_1049_1566 = (internal_copy_Octree x_907_1036_1553) in 
  let val y_921_1050_1567 = (internal_copy_Octree x_908_1037_1554) in 
  let val y_922_1051_1568 = (internal_copy_Octree x_909_1038_1555) in (Cell (x_897_1026_1543 , x_898_1027_1544, x_899_1028_1545, x_900_1029_1546, x_901_1030_1547, y_915_1044_1561, y_916_1045_1562, y_917_1046_1563, y_918_1047_1564, y_919_1048_1565, y_920_1049_1566, y_921_1050_1567, y_922_1051_1568)) end end end end end end end end 
  | Particle (x_923_1052_1569 , x_924_1053_1570, x_925_1054_1571) => (Particle (x_923_1052_1569 , x_924_1053_1570, x_925_1054_1571))
  | EmptyOct => EmptyOct);
val _ = (print(Int.toString(
  let val wildcard__13_16_1017_1532 = (printsym "Running program OctTree Physics Simulation: ") in 
  let val wildcard__11_17_1018_1533 = (printsym "NEWLINE") in 
  let val fltPrm_1439_1534 = 1 in 
  let val fltAppE_1438_1535 = (fltPrm_1439_1534 + 8) in 
  let val octTree_18_1019_1536 = (buildOctree(fltAppE_1438_1535 , 17, 0, 64)) in 
  let val wildcard__8_19_1020_1537 = (printsym "Running pass sumEnergy (fold, uses=12): ") in 
  let val wildcard__6_20_1021_1538 = (printsym "NEWLINE") in 
  let val totEnergy_21_1022_1539 = (sumEnergy octTree_18_1019_1536) in 
  let val wildcard__2_22_1023_1540 = (printsym "End") in 
  let val wildcard__0_23_1024_1541 = (printsym "NEWLINE") in totEnergy_21_1022_1539 end end end end end end end end end end)));
val _ = print "\n"
