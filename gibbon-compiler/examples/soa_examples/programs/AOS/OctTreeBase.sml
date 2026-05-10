datatype dat_Octree = Cell of (int  * int * int * int * int *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree) | Particle of (int  * int * int)| EmptyOct ;

fun internal_traverse_Octree (arg_1286_1600_1875) = (case arg_1286_1600_1875 of Cell (x_1287_1601_1876 , x_1288_1602_1877, x_1289_1603_1878, x_1290_1604_1879, x_1291_1605_1880, x_1292_1606_1881, x_1293_1607_1882, x_1294_1608_1883, x_1295_1609_1884, x_1296_1610_1885, x_1297_1611_1886, x_1298_1612_1887, x_1299_1613_1888) => 
  let val y_1305_1614_1889 = (internal_traverse_Octree x_1292_1606_1881) in 
  let val y_1306_1615_1890 = (internal_traverse_Octree x_1293_1607_1882) in 
  let val y_1307_1616_1891 = (internal_traverse_Octree x_1294_1608_1883) in 
  let val y_1308_1617_1892 = (internal_traverse_Octree x_1295_1609_1884) in 
  let val y_1309_1618_1893 = (internal_traverse_Octree x_1296_1610_1885) in 
  let val y_1310_1619_1894 = (internal_traverse_Octree x_1297_1611_1886) in 
  let val y_1311_1620_1895 = (internal_traverse_Octree x_1298_1612_1887) in 
  let val y_1312_1621_1896 = (internal_traverse_Octree x_1299_1613_1888) in () end end end end end end end end 
  | Particle (x_1313_1622_1897 , x_1314_1623_1898, x_1315_1624_1899) => ()
  | EmptyOct => ());

fun internal_print_Octree (arg_1319_1545_1820) = (case arg_1319_1545_1820 of Cell (x_1320_1546_1821 , x_1321_1547_1822, x_1322_1548_1823, x_1323_1549_1824, x_1324_1550_1825, x_1325_1551_1826, x_1326_1552_1827, x_1327_1553_1828, x_1328_1554_1829, x_1329_1555_1830, x_1330_1556_1831, x_1331_1557_1832, x_1332_1558_1833) => 
  let val wildcard_1346_1559_1834 = (print "(Cell") in 
  let val wildcard_1360_1560_1835 = (print " ") in 
  let val y_1333_1561_1836 = (print(Int.toString(x_1320_1546_1821))) in 
  let val wildcard_1359_1562_1837 = (print " ") in 
  let val y_1334_1563_1838 = (print(Int.toString(x_1321_1547_1822))) in 
  let val wildcard_1358_1564_1839 = (print " ") in 
  let val y_1335_1565_1840 = (print(Int.toString(x_1322_1548_1823))) in 
  let val wildcard_1357_1566_1841 = (print " ") in 
  let val y_1336_1567_1842 = (print(Int.toString(x_1323_1549_1824))) in 
  let val wildcard_1356_1568_1843 = (print " ") in 
  let val y_1337_1569_1844 = (print(Int.toString(x_1324_1550_1825))) in 
  let val wildcard_1355_1570_1845 = (print " ") in 
  let val y_1338_1571_1846 = (internal_print_Octree x_1325_1551_1826) in 
  let val wildcard_1354_1572_1847 = (print " ") in 
  let val y_1339_1573_1848 = (internal_print_Octree x_1326_1552_1827) in 
  let val wildcard_1353_1574_1849 = (print " ") in 
  let val y_1340_1575_1850 = (internal_print_Octree x_1327_1553_1828) in 
  let val wildcard_1352_1576_1851 = (print " ") in 
  let val y_1341_1577_1852 = (internal_print_Octree x_1328_1554_1829) in 
  let val wildcard_1351_1578_1853 = (print " ") in 
  let val y_1342_1579_1854 = (internal_print_Octree x_1329_1555_1830) in 
  let val wildcard_1350_1580_1855 = (print " ") in 
  let val y_1343_1581_1856 = (internal_print_Octree x_1330_1556_1831) in 
  let val wildcard_1349_1582_1857 = (print " ") in 
  let val y_1344_1583_1858 = (internal_print_Octree x_1331_1557_1832) in 
  let val wildcard_1348_1584_1859 = (print " ") in 
  let val y_1345_1585_1860 = (internal_print_Octree x_1332_1558_1833) in 
  let val wildcard_1347_1586_1861 = (print ")") in () end end end end end end end end end end end end end end end end end end end end end end end end end end end end 
  | Particle (x_1361_1587_1862 , x_1362_1588_1863, x_1363_1589_1864) => 
  let val wildcard_1367_1590_1865 = (print "(Particle") in 
  let val wildcard_1371_1591_1866 = (print " ") in 
  let val y_1364_1592_1867 = (print(Int.toString(x_1361_1587_1862))) in 
  let val wildcard_1370_1593_1868 = (print " ") in 
  let val y_1365_1594_1869 = (print(Int.toString(x_1362_1588_1863))) in 
  let val wildcard_1369_1595_1870 = (print " ") in 
  let val y_1366_1596_1871 = (print(Int.toString(x_1363_1589_1864))) in 
  let val wildcard_1368_1597_1872 = (print ")") in () end end end end end end end end
  | EmptyOct => 
  let val wildcard_1372_1598_1873 = (print "(EmptyOct") in 
  let val wildcard_1373_1599_1874 = (print ")") in () end end);

fun internal_copy_Octree (arg_1253_1374_1787) = (case arg_1253_1374_1787 of Cell (x_1254_1375_1788 , x_1255_1376_1789, x_1256_1377_1790, x_1257_1378_1791, x_1258_1379_1792, x_1259_1380_1793, x_1260_1381_1794, x_1261_1382_1795, x_1262_1383_1796, x_1263_1384_1797, x_1264_1385_1798, x_1265_1386_1799, x_1266_1387_1800) => 
  let val y_1272_1393_1806 = (internal_copy_Octree x_1259_1380_1793) in 
  let val y_1273_1394_1807 = (internal_copy_Octree x_1260_1381_1794) in 
  let val y_1274_1395_1808 = (internal_copy_Octree x_1261_1382_1795) in 
  let val y_1275_1396_1809 = (internal_copy_Octree x_1262_1383_1796) in 
  let val y_1276_1397_1810 = (internal_copy_Octree x_1263_1384_1797) in 
  let val y_1277_1398_1811 = (internal_copy_Octree x_1264_1385_1798) in 
  let val y_1278_1399_1812 = (internal_copy_Octree x_1265_1386_1799) in 
  let val y_1279_1400_1813 = (internal_copy_Octree x_1266_1387_1800) in (Cell (x_1254_1375_1788 , x_1255_1376_1789, x_1256_1377_1790, x_1257_1378_1791, x_1258_1379_1792, y_1272_1393_1806, y_1273_1394_1807, y_1274_1395_1808, y_1275_1396_1809, y_1276_1397_1810, y_1277_1398_1811, y_1278_1399_1812, y_1279_1400_1813)) end end end end end end end end 
  | Particle (x_1280_1401_1814 , x_1281_1402_1815, x_1282_1403_1816) => (Particle (x_1280_1401_1814 , x_1281_1402_1815, x_1282_1403_1816))
  | EmptyOct => EmptyOct);

