package software_verification;

public class Exercises {
	
	// I still get errors, even though this is basic AF
	// Removing the invariants doesn't seem to help at all
	/*@ ensures \result == (\forall int i; i>=0 && i<a.length; a[i] <= a[i+1]);
	 @ pure
	 */
	public static boolean is_sorted(int[] a) {
		boolean res = true;
		int k=0;
		
		//@ maintaining (res == (\forall int i; 0 <= i && i<k; a[i] <= a[i+1]));
		//@ decreasing a.length - (k+1);
		while(k+1 < a.length) {
			if(a[k] > a[k+1]) {
				res = false;
			}
			k++;
		}
		
		return res;
	}
	
	// No clue how to put result in the specifications
	// And the loop will kick my ass no matter what, I'm not even gonna try with it
	// I didn't mark this as a res because it didn't allow me to test the other part
	// Due to the previous issue of not knowing how to put res in the ensures
	
	/* ensures (\forall int i; i>=0 && i+1< res.length; res[i] <= res[i+1]);
	 @ requires (\forall int i; i>=0 && i+1< a.length; a[i] <= a[i+1]);
	 @ requires (\forall int i; i>=0 && i+1< b.length; b[i] <= b[i+1]);
	 */
	
	public static int[] merge_sorted(int[] a, int[] b) {
		int[] res = new int[a.length + b.length];
		int a_count = 0;
		int b_count = 0;
		int k = 0;
		
		while(k < res.length) {
			if(a_count >= a.length) {
				res[k] = b[b_count];
				b_count++;
			} else if (b_count >= b.length) {
				res[k] = a[a_count];
				a_count++;
			} else if(a[a_count] > b[b_count]) {
				res[k] = a[a_count];
				a_count++;
			} else {
				res[k] = b[b_count];
				b_count++;
			}
			
			++k;
		}
		
		return res;
	}
}
