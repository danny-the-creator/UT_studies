.data
	offset: .byte 4
	s: .byte 8		# sequence of numbers
.text
	main:
	move $t1, $zero
	move $t2, offset
	Loop_2:
	Loop_1:
	move $t4, $t0($t1)			# t0 - is the beginning of an array
	add $t3, $t1+$t2
	move $t5, $t0($t3)	
	# # Getting the Hamming Distance $t4, $t5		# here should be the code, which computes Hamming dist
	add $t2 $t2 offset
	mul $t6, offset, s
	bne $t3, $t6, Loop_1
	
	move $t2, offset
	addi $t1, $t1, offset
	add $t3, $t1+$t2
	bne $t3, $t6, Loop_2
	