#.data
#.align 2
#array:
#	.word 5, 2, 1, 10

.text
main:
	addi $s0, $zero, 8
	addi $s1, $zero, 1
	addi $s2, $zero, -8
	sllv $s3, $s0, $s1
	srlv $s3, $s2, $s1
	srav $s3, $s2, $s1
		
stop:

		
