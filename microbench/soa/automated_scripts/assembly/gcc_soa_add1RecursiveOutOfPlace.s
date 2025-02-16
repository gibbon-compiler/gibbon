0000000000001770 <add1RecursiveOutOfPlace>:
    1770:	48 89 d0             	mov    %rdx,%rax
    1773:	66 66 66 66 2e 0f 1f 	data16 data16 data16 cs nopw 0x0(%rax,%rax,1)
    177a:	84 00 00 00 00 00 
    1780:	48 8b 0f             	mov    (%rdi),%rcx
    1783:	0f b6 11             	movzbl (%rcx),%edx
    1786:	48 ff c1             	inc    %rcx
    1789:	48 89 0f             	mov    %rcx,(%rdi)
    178c:	48 8b 0e             	mov    (%rsi),%rcx
    178f:	88 11                	mov    %dl,(%rcx)
    1791:	48 ff 06             	incq   (%rsi)
    1794:	80 fa 30             	cmp    $0x30,%dl
    1797:	75 20                	jne    17b9 <add1RecursiveOutOfPlace+0x49>
    1799:	48 8b 4f 08          	mov    0x8(%rdi),%rcx
    179d:	8b 11                	mov    (%rcx),%edx
    179f:	48 83 c1 04          	add    $0x4,%rcx
    17a3:	48 89 4f 08          	mov    %rcx,0x8(%rdi)
    17a7:	ff c2                	inc    %edx
    17a9:	48 8b 4e 08          	mov    0x8(%rsi),%rcx
    17ad:	89 11                	mov    %edx,(%rcx)
    17af:	48 83 c1 04          	add    $0x4,%rcx
    17b3:	48 89 4e 08          	mov    %rcx,0x8(%rsi)
    17b7:	eb c7                	jmp    1780 <add1RecursiveOutOfPlace+0x10>
    17b9:	c3                   	ret    
    17ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
