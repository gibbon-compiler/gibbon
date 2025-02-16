0000000000401b70 <add1RecursiveOutOfPlace>:
  401b70:	48 89 d0             	mov    %rdx,%rax
  401b73:	48 8b 0f             	mov    (%rdi),%rcx
  401b76:	0f b6 11             	movzbl (%rcx),%edx
  401b79:	48 83 c1 01          	add    $0x1,%rcx
  401b7d:	48 89 0f             	mov    %rcx,(%rdi)
  401b80:	48 8b 0e             	mov    (%rsi),%rcx
  401b83:	88 11                	mov    %dl,(%rcx)
  401b85:	48 83 06 01          	addq   $0x1,(%rsi)
  401b89:	80 fa 30             	cmp    $0x30,%dl
  401b8c:	74 02                	je     401b90 <add1RecursiveOutOfPlace+0x20>
  401b8e:	c3                   	ret    
  401b8f:	90                   	nop
  401b90:	48 8b 57 08          	mov    0x8(%rdi),%rdx
  401b94:	8b 0a                	mov    (%rdx),%ecx
  401b96:	48 83 c2 04          	add    $0x4,%rdx
  401b9a:	48 89 57 08          	mov    %rdx,0x8(%rdi)
  401b9e:	48 8b 56 08          	mov    0x8(%rsi),%rdx
  401ba2:	83 c1 01             	add    $0x1,%ecx
  401ba5:	89 0a                	mov    %ecx,(%rdx)
  401ba7:	48 83 c2 04          	add    $0x4,%rdx
  401bab:	48 89 56 08          	mov    %rdx,0x8(%rsi)
  401baf:	eb c2                	jmp    401b73 <add1RecursiveOutOfPlace+0x3>
  401bb1:	66 66 2e 0f 1f 84 00 	data16 cs nopw 0x0(%rax,%rax,1)
  401bb8:	00 00 00 00 
  401bbc:	0f 1f 40 00          	nopl   0x0(%rax)
