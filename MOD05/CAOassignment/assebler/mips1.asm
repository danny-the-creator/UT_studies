.data
	prompt:  .asciiz "Enter a number (32 bits max) in decimal: "
	result: .asciiz "You have the following Hamming Distances in this order 1-2, 1-3, 1-4, 2-3, 2-4, 3-4:  "
	separator: .asciiz ", "
.text
	main: 
	# The first number
	li $v0, 4            # syscall for print string
    	la $a0, prompt
    	syscall              # print the prompt
	
	li $v0, 5            # syscall for read integer
    	syscall              
    	move $t0, $v0	     # read input from user, result in $t0
    	
    	
    	# The second number (same as above)
    	li $v0, 4            
    	la $a0, prompt       
    	syscall              
    	
    	li $v0, 5           
    	syscall              # read input from user, result in $t1
    	move $t1, $v0
    	
    	
    	# The third number (same as above)
    	li $v0, 4            
    	la $a0, prompt       
    	syscall              
    	
    	li $v0, 5            
    	syscall              # read input from user, result in $t2
    	move $t2, $v0
    	
    	
    	# The fourth number (same as above)
    	li $v0, 4            
    	la $a0, prompt       
    	syscall             
    	
    	li $v0, 5            
    	syscall              # read input from user, result in $t3
    	move $t3, $v0
    	
    	
    	
	li $v0, 4		# syscall for print string
    	la $a0, result      
    	syscall			# print the result prompt
    	
    	
    	# Getting the Hamming Distance (1-2)
    	xor $t5, $t0, $t1	# The quantity of ones in XOR will be the Hamming Distance between given numbers
    	
	# Count number of ones
    	bit_loop_12:
        andi $t6, $t5, 0x1       # Mask the least significant bit (LSB) and write the result into $t6
        add $t7, $t7, $t6         # $t7 is a counter, if LSB ($t6) is one, then it is increased; 
        								# otherwise, nothing changes
        srl $t5, $t5, 1		# shift right to proceed to the next bit
        bne $t5, $zero, bit_loop_12    # Exit loop if $t5 becomes 0 (all non-zero bits processed)
    	
    	move $a0, $t7
    	li $v0, 1            # syscall for print integer
	syscall			# print calculated Haming distance
	
	li $v0, 4            # syscall for print string
    	la $a0, separator    
    	syscall              # print the separator between distances
    	
    	move $t7, $zero		# reset the variable
    	
    	# Getting the Hamming Distance (1-3) same as above
    	xor $t5, $t0, $t2
    	
    	# Count number of ones
    	bit_loop_13:
        andi $t6, $t5, 0x1       
        add $t7, $t7, $t6        
        
        srl $t5, $t5, 1
        bne $t5, $zero, bit_loop_13   
        
        move $a0, $t7
    	li $v0, 1           
	syscall
	
	li $v0, 4            
    	la $a0, separator       
    	syscall 
    	
    	move $t7, $zero	            
    	
        # Getting the Hamming Distance (1-4) same as above
        xor $t5, $t0, $t3
    	
    	# Count number of ones
    	bit_loop_14:
        andi $t6, $t5, 0x1       
        add $t7, $t7, $t6         
        
        srl $t5, $t5, 1
        bne $t5, $zero, bit_loop_14    
        
        move $a0, $t7
    	li $v0, 1           
	syscall
	
	li $v0, 4           
    	la $a0, separator      
    	syscall  
    	
    	move $t7, $zero            
    	
        # Getting the Hamming Distance (2-3) same as above
        xor $t5, $t1, $t2
    	
    	# Count number of ones
    	bit_loop_23:
        andi $t6, $t5, 0x1       
        add $t7, $t7, $t6        
        
        srl $t5, $t5, 1
        bne $t5, $zero, bit_loop_23    
        
        move $a0, $t7
    	li $v0, 1           
	syscall
	
	li $v0, 4     
    	la $a0, separator      
    	syscall 
    	
    	move $t7, $zero              
        
        # Getting the Hamming Distance (2-4) same as above
	xor $t5, $t1, $t3
    	
    	# Count number of ones
    	bit_loop_24:
        andi $t6, $t5, 0x1       
        add $t7, $t7, $t6        
        
        srl $t5, $t5, 1
        bne $t5, $zero, bit_loop_24    
    	
    	move $a0, $t7
    	li $v0, 1       
	syscall
    	
    	li $v0, 4            
    	la $a0, separator    
    	syscall 
    	
    	move $t7, $zero              
    	
    	# Getting the Hamming Distance (3-4) same as above, but without separator
	xor $t5, $t2, $t3
    	
    	# Count number of ones
    	bit_loop_34:
        andi $t6, $t5, 0x1       
        add $t7, $t7, $t6         
        
        srl $t5, $t5, 1
        bne $t5, $zero, bit_loop_34    
    
	move $a0, $t7
    	li $v0, 1
	syscall 
    	
    	move $t7, $zero
	
	
	