public class Maximization {

	/* Return the maximum of x1, x2 and x3. 
	 * Does not change the arguments.
	 */
	/*@ 
	  @ ensures \result >= x1; 
	  @ ensures \result >= x2; 
	  @ ensures \result >= x3;
	  @ ensures \result >= x1 && \result >= x2 && \result >= x3;
	  @ ensures \result == x1 || \result == x2 || \result == x3;
	*/
	public static int max(int x1, int x2, int x3) {
		if (x1>=x2 && x1 >= x3) { return x1; }
		else if (x2>=x3) { return x2; }
		else { return x3; }
	}
	
	/*@ 
	  @ ensures \result >= x1; 
	  @ ensures \result >= x2; 
	  @ ensures \result >= x3;
	  @ ensures \result == x1 || \result == x2 || \result == x3;
	*/
	public static int bad_max(int x1, int x2, int x3) {
		if (x1>=x2) { return x1; }
		else if (x2>=x3) { return x2; }
		else { return x3; }
	}
	
	/*@ 
	  @ requires 0<a.length;
	  @ ensures (\forall int i; 0<=i && i<a.length; \result >= a[i]);
	  @ ensures (\exists int i; 0<=i && i<a.length; \result == a[i]);
	*/
	public static int max(int[] a) {
		int n=a.length;
		// assert (n>0);
		int r=a[0];
		int k=1;
		//@ maintaining (\forall int i; 0<=i && i<k; r >= a[i]);
		//@ maintaining (\exists int i; 0<=i && i<k; r == a[i]);
		//@ maintaining k<=n;
		//@ decreasing n-k;
		while (k!=n) {
			if (a[k]>r) { r=a[k]; }
			k=k+1;
		}
		return r;
	}
	
    

}
