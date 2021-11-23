package hoare_logic;

import java.util.Arrays;

public class Exercises {
	
	/*@ ensures a[i] = \old a[j]
	 *@ ensures a[j] = \old a[i]
	 *
	 */
	public static void swap(int[] a, int i, int j) {
		int temp = a[i];
		a[i] = a[j];
		a[j] = temp;
	}

	public static void main(String[] args) {
		// TODO Auto-generated method stub
		int[] temp = {1,2,3,4,5,6};
		swap(temp, 1, 2);
		System.out.print(Arrays.toString(temp));

	}

}
