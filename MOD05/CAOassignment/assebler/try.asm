.data
separator: .asciiz ", "   # Store the separator string with null termination
sep_addr: .word separator  # Store the address of the separator string


seq_: .word 5    # sequence of numbers
len_: .word 32

.text
.globl main

main:
    # Directly initialize values for n and b
    
    lw  $t1, seq_          # Load number of elements (n)
    addi $t2, $zero, 4
    move $t5, $zero        # Initialize $t5 to 0 (total bytes to allocate)
    move $t3, $t1          # Move n to $t3 for the loop counter


add_bytes:
    add $t5, $t5, $t2        # $t5 += $t2 (4)
    addi $t3, $t3, -1       # Decrement the counter ($t3) by 1
    bne $t3, $zero, add_bytes  # If $t3 (counter) != 0, go to add_bytes

    # Syscall to allocate memory dynamically using sbrk
    addi $v0, $zero, 9             # Syscall number for sbrk
    move $a0, $t5         # Pass total bytes to allocate
    syscall               # Allocate memory
    move $s0, $v0         # Save base address of the allocated memory in $s0




    # Input loop to get 'n' numbers from the user and store them in the array
    move $t6, $s0         # $t6 will be the pointer to the current array element
    move $t7, $zero       # Initialize the loop counter ($t7 = 0)


input_loop:

    # Read an integer from the user
    addi $v0,$zero, 5                    # Syscall for reading an integer
    syscall
    move $t0, $v0                # Store the input value in $t0

    # Store the value into the dynamically allocated array (4 bytes per number)
    sw $t0, 0($t6)               # Store the input in the current position in array

    # Move to the next element in the array (advance by 4 bytes)
    add $t6, $t6, $t2             # Increment pointer by 4 bytes
    addi $t7, $t7, 1            # Increment loop counter 
    bne $t7, $t1, input_loop  # If counter != n, continue the loop


# Find all combinations
  move $t0, $t2  # offset - $t0
  move $t1, $zero
  move $t6, $t5  # $t6 - len array
  Loop:
  add $t4, $t1, $s0
  lw $t4, 0($t4)  # !    # s0 - is the beginning of an array
  add $t3, $t1, $t2
 
  add $t5, $t3, $s0
  lw $t5, 0($t5)  # !
  # # Getting the Hamming Distance $t4, $t5    
  
  xor $t4, $t4, $t5      # Calculate the Hamming distance
  move $t7, $zero         # Initialize counter to 0

# Start counting ones in the number

count_ones:
    move $t3, $zero
    addi $t7, $t7, 1            # Increment the counter
    addi $t3, $t4, -1             # Subtract 1 from $t4
    and $t4, $t4, $t3             # This will effectively remove the lowest set bit
    bne $t4, $zero, count_ones   # If $t4 is not zero, continue counting

    move $a0, $t7                 # Move the count of ones into $a0 for printing
    addi $v0, $zero, 1                     # Syscall for print integer
    syscall                        # Print the count of ones

# Print the separator
    addi $v0, $zero, 4                     # Syscall for print string
    lw $a0, sep_addr              # Load the address of the separator string into $a0
    syscall                       # Print the separator

      #-------------------------------------------------------------------------------
  
  add $t2, $t2, $t0
  add $t3, $t1, $t2
  bne $t3, $t6, Loop
  
  move $t2, $t0
  add $t1, $t1, $t0
  add $t3, $t1, $t2
  bne $t3, $t6, Loop

  addi $v0,$zero, 10                # Syscall to exit
  syscall