package com.t2.t2sensorlib;

import android.app.ActivityManager;
import android.app.KeyguardManager;
import android.app.Notification;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.app.Service;
import android.bluetooth.BluetoothAdapter;
import android.bluetooth.BluetoothDevice;
import android.content.BroadcastReceiver;
import android.content.ContentResolver;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.content.pm.PackageInfo;
import android.content.pm.PackageManager;
import android.content.res.Configuration;
import android.database.ContentObserver;
import android.database.Cursor;
import android.hardware.Sensor;
import android.hardware.SensorEvent;
import android.hardware.SensorEventListener;
import android.hardware.SensorManager;
import android.location.Location;
import android.location.LocationListener;
import android.location.LocationManager;
import android.net.Uri;
import android.net.wifi.ScanResult;
import android.net.wifi.WifiInfo;
import android.net.wifi.WifiManager;
import android.os.AsyncTask;
import android.os.BatteryManager;
import android.os.Binder;
import android.os.Build;
import android.os.Bundle;
import android.os.Handler;
import android.os.IBinder;
import android.os.Parcel;
import android.os.PowerManager;
import android.os.RemoteException;
import android.provider.Browser;
import android.telephony.PhoneStateListener;
import android.telephony.SmsMessage;
import android.telephony.TelephonyManager;
import android.telephony.cdma.CdmaCellLocation;
import android.telephony.gsm.GsmCellLocation;
import android.util.Log;
import android.widget.Toast;

import org.codehaus.jackson.node.ArrayNode;
import org.codehaus.jackson.node.JsonNodeFactory;
import org.codehaus.jackson.node.ObjectNode;
import org.t2health.lib1.DataOutHandler;
import org.t2health.lib1.SharedPref;
import org.t2health.lib1.DataOutHandler.DataOutPacket;
import com.example.t2sensorlib.R;
//import com.t2.bigbrother.R;
import com.t2.t2sensorlib.Receiver.OnBioFeedbackMessageRecievedListener;



import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.Iterator;
import java.util.List;
import java.util.Locale;
import java.util.Set;


/**
 * @author scott.coleman
 * 
 * BigBrotherService is a background service that polls parameters and saves them to disk as well as sending them
 * to the external database.
 * 
 * BigBrotherService is started up by the main activity once every mBaseSamplePeriod seconds (defaults to 10 seconds).
 * It then continues to run as long as it detects activity.
 * If it does not detect activity for mSecondsWithoutActivityThreshold seconds it will exit.
 *
 */
public class BigBrotherService extends Service implements SensorEventListener, LocationListener, OnBioFeedbackMessageRecievedListener {

	private static final String TAG = "BigBrotherService";
	
	/**
	 * Static names dealing with the external database
	 */
	public static final String dDatabaseName = "bigbrother-sync";
	public static final String dDesignDocName = "bigbrother-local";
	public static final String dDesignDocId = "_design/" + dDesignDocName;
	public static final String byDateViewName = "byDate";

	private static final String mAppId = "BigBrotherService";	
	
	
	private String mLastSentSMSMd5 = "";
	/**
	 * Monitors  for new inbound and outbound SMS
	 */
	private SMSObserver mMySMSObserver;	
	
	/**
	 * Default Server database to sync to
	 * Not: to change this change it in strings.xml
	 */
	private String mDefaultRemoteDatabaseUri;	
	
	/**
	 * Database uri that the service will sync to 
	 */
	private String mRemoteDatabaseUri;	
	
	// ------------------------------------------------- 
	// Preference variables
	// ------------------------------------------------- 
	/**
	 * Time between samples when actively sampling
	 */
	private int mSampleAveragePeriodMS = 1000;		// milliseconds	

	/**
	 * Time to wait before declaring no activity
	 */
	private int mSecondsWithoutActivityThreshold = 5;	// seconds

	/**
	 * Time to wait before starting sampling 
	 */
	private int mPollingPeriod = 30;		// seconds
	
	/**
	 * Not used right now
	 */
	private boolean mKeepAppAlive = false;

	/**
	 * Whether or not to record samples to database
	 */
	private boolean mDatabaseEnabled = false;

	/**
	 * Used to enable/disable periodic sampling. This can be useful to disable all but event driven samples (calls, messages, etc)
	 */
	private boolean mSamplingEnabled = false;

	/**
	 * Whether or not to exit service between sample polling
	 * We're using this right now to avoid an issue in TouchDB where if we exit the service the database breaks
	 */
	private boolean mContinousService = false;
	
	/**
	 * Threshold for acceleration to determine if there is activity or not. 
	 */
	private double mAccelerationThreshold = 12.0;
	private double mMaxTotalAcceleration;
	private boolean mActivityDetected = false;	
	private int mSecondsWithoutActivity = 0;
	
	private int mBatteryLevel = 0;
	private int mBatteryStatus = 0;
	
	/**
	 * Command receiver for receiving commands from main activity
	 * @see onReceived()
	 */
	private Receiver commandReceiver;	

	private boolean mSamplingActive = false;

	/**
	 * Class to help in saving received data to file
	 */
	private DataOutHandler mDataOutHandler;	
	
	private NotificationManager mNotificationManager = null;
	private SensorManager mSensorManager = null;
	
	private float[] mAccelerometerAccumulator = new float[3];
	private int mAccelerometerAccumulatorCount = 0;

	private float[] mOrientationAccumulator = new float[3];
	private int mOrientationAccumulatorCount = 0;

	private float mLightAccumulator = 0;
	private float mLightAccumulatorCount = 0;
	
	private float mProximityAccumulator = 0;
	private float mProximityAccumulatorCount = 0;
	
	private float mTotalAccereration = 0;
	
	private float[] gravity = new float[3];
	private float[] linear_acceleration = new float[3];
	
	/**
	 * GPS location fix handler
	 */
	private LocationManager mLocationManager;

	/**
	 * Most recent GPS fix
	 */
	private Location mLocationFix;

	
	/**
	 * Used to abort periodic samling
	 */
	private boolean mAbortService = false;
	
	TelephonyManager mTelephonyManager;	

	/**
	 * Drives the phone call state machine. 
	 * For tracking phone calls start/progress/end
	 */
	PhoneStateListener mPhoneStateListener;	

	/**
	 * Monitors for new web page navigation
	 */
	private T2BrowserObserver mT2Observer;	

	/**
	 * URI for T2BrowserObserver
	 */
	private Uri mBrowserUri;
	
	/**
	 * Most recently browsed URL
	 */
	private String mLastBrowserUrl = "";
	
	/**
	 * The most recently navigated to URL
	 * This is used by sampleParemeters to determine if there is a URL to log
	 */
	String currentUrl = null;	
	
	
	/**
	 * @author scott.coleman
	 * 
	 * Class for tracking all relevant information related to 
	 * SMS or MMS text messages 
	 */
	public class TextMessage {
		
		TextMessage() {
			mDate = System.currentTimeMillis();
			mDirection = "";
			mLength = 0;
			mBody = "";
			mType = "";
			mRemoteNumber = "";
		}
		public String mDirection;	// "in" or "out"
		public String mType;	// "sms" or "mms"
		public long mDate;		// Unix time + milliseconds
		public int mLength;
		public String mBody;
		public String mRemoteNumber;
	}
	
	/**
	 * The most recently received SMS message
	 */
	TextMessage currentSMSMessage = null;	

	/**
	 * The most recently received MMS message
	 */
	TextMessage currentMMSMessage = null;	
	
	
	/**
	 * @author scott.coleman
	 * 
	 * Class for tracking all relevant information related to 
	 * phone calls 
	 */
	public class PhoneCall {
		public static final int T2_STATE_IDLE = TelephonyManager.CALL_STATE_IDLE;
		public static final int T2_STATE_OFFHOOK = TelephonyManager.CALL_STATE_OFFHOOK;
		public static final int T2_STATE_RINGING = TelephonyManager.CALL_STATE_RINGING;
		public static final int T2_STATE_OUTBOUND = 0x1000;
		
		PhoneCall() {
			mStartTime = System.currentTimeMillis();
			mDirection = "";
			mDuration = 0;
			mRemoteNumber = "";
		}
		public String mDirection;	// "in" or "out"
		public long mStartTime;		// Milliseconds
		public int mDuration;		// Seconds
		public String mRemoteNumber;
	}
	
	/**
	 * The most recently received phone call
	 */
	PhoneCall mCurrentPhoneCall = null;

	/**
	 * Used to track the state if the one and only phone call being tracked 
	 */
	public int mCurrentPhoneCallState = PhoneCall.T2_STATE_IDLE;;			// TelephonyManager.CALL_STATE_XXXX 
	
	
	
    @Override
    public void onCreate() {
    	Log.i(TAG, this.getClass().getSimpleName() + ".onCreate()");     	
		Log.e(TAG, "STARTING service");   									// TODO: remove
    	
		mTelephonyManager = (TelephonyManager) this.getSystemService(Context.TELEPHONY_SERVICE);

    	//mNotificationManager = (NotificationManager)getSystemService(NOTIFICATION_SERVICE);

		// ----------------------------------------------------
		// Load preference variable from shared preferences
		// ----------------------------------------------------
        mSamplingEnabled = SharedPref.getBoolean(this, "sampling_enabled", true);
        Log.i(TAG, "sampling_enabled = " + mSamplingEnabled);
        
        mDatabaseEnabled = SharedPref.getBoolean(this, "database_enabled", true); 
        Log.i(TAG, "dataabase_enabled = " + mDatabaseEnabled);

        mKeepAppAlive = SharedPref.getBoolean(this, "keep_app_alive", true); 
        Log.i(TAG, "keep_app_alive = " + mKeepAppAlive);

		mDefaultRemoteDatabaseUri = getResources().getString(R.string.database_uri);	
        mRemoteDatabaseUri = SharedPref.getString(this, "database_sync_name", mDefaultRemoteDatabaseUri);
        Log.i(TAG, "Remote database Uri = " + mRemoteDatabaseUri);

        mContinousService = SharedPref.getBoolean(this, "continous_service", true);
        Log.i(TAG, "Continous Service = " + mContinousService);

		mPollingPeriod = Integer.parseInt(SharedPref.getString(this, "polling_period", "30"));		
		Log.i(TAG, "Polling Period = " + mPollingPeriod);
		
		mSecondsWithoutActivityThreshold = Integer.parseInt(SharedPref.getString(this, "inactivity_timeout", "5"));		
		Log.i(TAG, "Inactivity Timeout = " + mSecondsWithoutActivityThreshold);
		
		mAccelerationThreshold = Float.parseFloat(SharedPref.getString(this, "activity_threshold", "12.0"));		
		Log.i(TAG, "Acceleration threshold= " + mAccelerationThreshold + " m/s^2");
        
        
        mAbortService = false;    	
        
		SimpleDateFormat sdf = new SimpleDateFormat("yyyy-MM-dd", Locale.US);
		String sessionDate = sdf.format(new Date());
		String userId = SharedPref.getString(this, "SelectedUser", 	"");
		long sessionId = SharedPref.getLong(this, "bio_session_start_time", 0);
		String appName = SharedPref.getString(this, "app_name", mAppId);
		
		// ----------------------------------------------------
		// Create a data handler to handle outputting data
		//	to files and database
		// ----------------------------------------------------		
		try {
			mDataOutHandler = new DataOutHandler(this, userId,sessionDate, appName, DataOutHandler.DATA_TYPE_INTERNAL_SENSOR, sessionId );
			mDataOutHandler.enableLogging(this);
			mDataOutHandler.enableLogCat();
			Log.d(TAG, "Initializing DataoutHandler"); // TODO: remove
		} catch (Exception e1) {
			Log.e(TAG, e1.toString());
			e1.printStackTrace();
		}    	

		
		if (mDatabaseEnabled) {
			mTelephonyManager = (TelephonyManager) this.getSystemService(Context.TELEPHONY_SERVICE);
	   		String myNumber = mTelephonyManager.getLine1Number();
	   		
	   		mRemoteDatabaseUri += myNumber; 
	   		
			Log.d(TAG, "Initializing database at " + mRemoteDatabaseUri); // TODO: remove
			mDataOutHandler.initializeDatabase(dDatabaseName, dDesignDocName, dDesignDocId, byDateViewName, mRemoteDatabaseUri);
		}		
		
		// Log the version
		try {
			PackageManager packageManager = getPackageManager();
			PackageInfo info = packageManager.getPackageInfo(getPackageName(), 0);			
			String applicationVersion = info.versionName;
			String versionString = mAppId + " application version: " + applicationVersion;

			DataOutPacket packet = mDataOutHandler.new DataOutPacket();
			packet.add("version", versionString);
			mDataOutHandler.handleDataOut(packet);				

		}
		catch (Exception e) {
		   	Log.e(TAG, e.toString());
		} 		
    	
        if (mNotificationManager != null) {
        	showNotification();		// show the icon in the status bar
        }
        
        mSensorManager = (SensorManager) getSystemService(SENSOR_SERVICE);  
        
        // Start up the thread running the service.  Note that we create a
        // separate thread because the service normally runs in the process's
        // main thread, which we don't want to block.
        Thread thr = new Thread(null, mTask, "BigBrotherService");
        thr.start();
        
        // Add a command receiver to receive commands from the main activity
        this.commandReceiver = new Receiver(this);        

        // -----------------------------------------------------
        // Start listeners for calls, messages and sensors
        // -----------------------------------------------------
        IntentFilter filter = new IntentFilter();		
		filter.addAction("android.intent.action.PHONE_STATE");
		filter.addAction("android.intent.action.NEW_OUTGOING_CALL");
        this.registerReceiver(this.callReceiver, filter);        
        
        // Start message listeners
//		IntentFilter filter = new IntentFilter();		
//		filter.addAction("android.provider.Telephony.SMS_RECEIVED");
//		filter.addAction("android.provider.Telephony.WAP_PUSH_RECEIVED");
//		filter.addAction("android.provider.Telephony.MMS_RECEIVED");
//        this.registerReceiver(this.messageReceiver, filter);        
        Handler handle = new Handler(){};
        mMySMSObserver = new SMSObserver(handle);
        ContentResolver contentResolver = getContentResolver();
        contentResolver.registerContentObserver(Uri.parse("content://sms"),true, mMySMSObserver);
//        contentResolver.registerContentObserver(Uri.parse("content://mms-sms"),true, mMySMSObserver);		
        
        // Start listener for browser
        mBrowserUri = Uri.parse("content://browser/history");          
        mT2Observer = new T2BrowserObserver(handle);
        contentResolver.registerContentObserver(mBrowserUri,true, mT2Observer);          
        
        
        
        
        this.registerReceiver(this.batteryInfoReceiver,	new IntentFilter(Intent.ACTION_BATTERY_CHANGED));        
		this.registerReceiver(this.commandReceiver,new IntentFilter(Constants.ACTION_COMMAND_BROADCAST)); 

    	mSensorManager.registerListener(this, mSensorManager.getDefaultSensor(Sensor.TYPE_ACCELEROMETER), SensorManager.SENSOR_DELAY_GAME);
    	mSensorManager.registerListener(this, mSensorManager.getDefaultSensor(Sensor.TYPE_ORIENTATION), SensorManager.SENSOR_DELAY_GAME);		
    	mSensorManager.registerListener(this, mSensorManager.getDefaultSensor(Sensor.TYPE_LIGHT), SensorManager.SENSOR_DELAY_GAME);		
    	mSensorManager.registerListener(this, mSensorManager.getDefaultSensor(Sensor.TYPE_PROXIMITY), SensorManager.SENSOR_DELAY_GAME);		
		
    	// GPS Location
    	if (SharedPref.getBoolean(this, "location", true)) {
	    	mLocationManager = (LocationManager) getSystemService(Context.LOCATION_SERVICE);
	    	mLocationManager.requestLocationUpdates(LocationManager.GPS_PROVIDER, 1000L, 0, this);    	
    	}
    }

    @Override
	public void onStart(Intent intent, int startId) {
		super.onStart(intent, startId);
    	Log.i(TAG, this.getClass().getSimpleName() + ".onStart()");
        mAbortService = false;    	
    	
    	
        mSamplingEnabled = SharedPref.getBoolean(this, "sampling_enabled", true);
        mKeepAppAlive = SharedPref.getBoolean(this, "keep_app_alive", true); 
        mRemoteDatabaseUri = SharedPref.getString(this, "database_sync_name", mDefaultRemoteDatabaseUri);
        mDatabaseEnabled = SharedPref.getBoolean(this, "database_enabled", true); 
        mContinousService = SharedPref.getBoolean(this, "continous_service", true);
    	
		Log.e(TAG, "Start active sampling"); 
    	mSamplingActive = true;    	
    	mSecondsWithoutActivity = 0;    	
	}

	@Override
    public void onDestroy() {
    	Log.i(TAG, this.getClass().getSimpleName() + ".onDestroy()");     	
    	
        mDataOutHandler.close();
//	    mTelephonyManager.listen(mPhoneStateListener, PhoneStateListener.LISTEN_NONE);
        
    	
        if (mNotificationManager != null) {
        	// 	Cancel the notification -- we use the same ID that we had used to start it
        	mNotificationManager.cancel(R.string.service_started);
        }
        
        mSensorManager.unregisterListener(this, mSensorManager.getDefaultSensor(Sensor.TYPE_ACCELEROMETER));
        mSensorManager.unregisterListener(this, mSensorManager.getDefaultSensor(Sensor.TYPE_ORIENTATION));   
        mSensorManager.unregisterListener(this, mSensorManager.getDefaultSensor(Sensor.TYPE_LIGHT));   
        mSensorManager.unregisterListener(this, mSensorManager.getDefaultSensor(Sensor.TYPE_PROXIMITY));   

        // Stop message listeners
        //    	this.unregisterReceiver(this.messageReceiver);
        ContentResolver contentResolver = getContentResolver();
        contentResolver.unregisterContentObserver(mMySMSObserver);		
        
        // Stop listener for browser    
        contentResolver.unregisterContentObserver(mT2Observer);	         
        
    	this.unregisterReceiver(this.callReceiver);
    	this.unregisterReceiver(this.batteryInfoReceiver);
    	this.unregisterReceiver(this.commandReceiver);		
    	
    	if (mLocationManager != null) {
    		mLocationManager.removeUpdates(this);
    	}

        // Tell the user we stopped.
    	if (mKeepAppAlive) {
            Toast.makeText(this, R.string.service_finished, Toast.LENGTH_SHORT).show();
    	}
    }
	
	
	// TODO:
	// Create new file each new day and Q the previous log files to send to the database
	void doFileMaintenance() {
		
	}

	/**
     * The function that runs in our worker thread
     * This is the main periodic sampling thread
     */
    Runnable mTask = new Runnable() {
        public void run() {
            long endTime = System.currentTimeMillis() + 2 * 1000;
            while (System.currentTimeMillis() < endTime) {
                synchronized (mBinder) {
                    try {
                    	// Decide whether or not to send data and to change file name for new day
                    	doFileMaintenance();                    	
               			while(true) {
                            //mBinder.wait(endTime - System.currentTimeMillis());
               				Thread.sleep(mSampleAveragePeriodMS);
               				
               				if (mAbortService) {
               					break;
               				}
               				if (mSamplingActive) {
               					try {
               						if (mSamplingEnabled) {
    									sampleParameters();
               						}               						
								} catch (Exception e) {
									Log.e(TAG, e.toString());
									e.printStackTrace();
								}
               				}
               				
               				if (!mActivityDetected) {
               					mSecondsWithoutActivity++;
               					
               					if ((mSecondsWithoutActivity >= mSecondsWithoutActivityThreshold)  && mSamplingActive) {
               						if (mContinousService) {
               							mDataOutHandler.purgeLogFile();
                   						mSamplingActive = false;
               							mSecondsWithoutActivity = 0;
                   						Log.e(TAG, "" + mSecondsWithoutActivityThreshold + " seconds without activity - cancel active sampling"); 
               						}
               						else {
                   						Log.e(TAG, "" + mSecondsWithoutActivityThreshold + " seconds without activity - exiting service"); 
                   						break;
               						}
               					}
               				} else {
            	            	Log.d(TAG, "Activity detected");
               				}
               				
               				mActivityDetected = false;
               			} // End while(true)
                    } catch (Exception e) {
                    }
                }
            }
			Log.e(TAG, "Waiting 10 seconds before stopping service");   

			try {
				Thread.sleep(10000);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
			Log.e(TAG, "Stopping service now");   
            
            // Done with our work...  stop the service!
            BigBrotherService.this.stopSelf();
        }
    };

    @Override
    public IBinder onBind(Intent intent) {
        return mBinder;
    }

    /**
     * Show a notification while this service is running.
     */
    private void showNotification() {
        // In this sample, we'll use the same text for the ticker and the expanded notification
//        CharSequence text = getText(R.string.service_started);
//
//        // Set the icon, scrolling text and timestamp
//        Notification notification = new Notification(R.drawable.stat_sample, text,
//                System.currentTimeMillis());
//
//        // The PendingIntent to launch our activity if the user selects this notification
////        PendingIntent contentIntent = PendingIntent.getActivity(this, 0,
////                new Intent(this, T2BigBrotherActivity.class), 0);
//
//        // Set the info for the views that show in the notification panel.
//        notification.setLatestEventInfo(this, getText(R.string.service_label),
//                       text, contentIntent);
//
//        // Send the notification.
//        // We use a layout id because it is a unique number.  We use it later to cancel.
//        if (mNotificationManager != null) {
//        	mNotificationManager.notify(R.string.service_started, notification);
//        }
    }

    /**
     * This is the object that receives interactions from clients.  See RemoteService
     * for a more complete example.
     */
    private final IBinder mBinder = new Binder() {
        @Override
		protected boolean onTransact(int code, Parcel data, Parcel reply,
		        int flags) throws RemoteException {
            return super.onTransact(code, data, reply, flags);
        }
    };

	@Override
	public void onAccuracyChanged(Sensor sensor, int accuracy) {
		// TODO Auto-generated method stub
	}

	@Override
	public void onSensorChanged(SensorEvent event) {
	    synchronized (this) {
	        switch (event.sensor.getType()){
	        
	        case Sensor.TYPE_PROXIMITY:
        			mProximityAccumulator += event.values[0];
        			mProximityAccumulatorCount++;
        			break;
	        	
	        	case Sensor.TYPE_LIGHT:
	        		mLightAccumulator += event.values[0];
	        		mLightAccumulatorCount++;
	        		break;

	            case Sensor.TYPE_ACCELEROMETER:

	            	double totalAcceleration = Math.sqrt(
	            			event.values[0] * event.values[0] + 
	            			event.values[1] * event.values[1] + 
	            			event.values[2] * event.values[2] 
	            	);
	            	//Log.i(TAG, "totalAcceleration = " + totalAcceleration);
	            	
	            	// Keep track of the max acceleration for this sample period
	            	if (totalAcceleration > mMaxTotalAcceleration)
	            		mMaxTotalAcceleration = totalAcceleration;
	            	
	            	mAccelerometerAccumulator[0] += event.values[0]; 
	            	mAccelerometerAccumulator[1] += event.values[1]; 
	            	mAccelerometerAccumulator[2] += event.values[2]; 
	            	mAccelerometerAccumulatorCount++;	            	
	            break;
	        case Sensor.TYPE_ORIENTATION:
            	mOrientationAccumulator[0] += event.values[0]; 
            	mOrientationAccumulator[1] += event.values[1]; 
            	mOrientationAccumulator[2] += event.values[2]; 
            	mOrientationAccumulatorCount++;	            	
	        break;
	 
	        } // End switch (event.sensor.getType()){
	    } // End synchronized (this) {
	}
	
	/**
	 * We get here every mSampleAveragePeriodMS milliseconds (defaults to 1 second)
	 * We sample all parameters here that require periodic sampling 
	 * 
	 * Note that some parameters (like acclerometer) report so quickly that we need to average their output
	 * This is handled by variables 
     * 	mxxxxAccumulatorCount
     *  mxxxxAccumulator[n] 
	 */	
	private void sampleParameters() {
//		Log.e(TAG, "Recording Sample");   
		
	    synchronized (this) {
	    	ObjectNode dataNode = JsonNodeFactory.instance.objectNode();
	    	
	   		// ------------------------------
	    	// Accelerometer
	    	// ------------------------------
	    	if (SharedPref.getBoolean(this, "accelerometer", true)) {
		    	if (mAccelerometerAccumulatorCount > 0) {
		        	ObjectNode inner = JsonNodeFactory.instance.objectNode();    	
					inner.put("Z", mAccelerometerAccumulator[2]/mAccelerometerAccumulatorCount);
					inner.put("Y", mAccelerometerAccumulator[1]/mAccelerometerAccumulatorCount);
					inner.put("X", mAccelerometerAccumulator[0]/mAccelerometerAccumulatorCount);
					dataNode.put("ACCELEROMETER", inner);
		        	
		        	mAccelerometerAccumulatorCount = 0;
		        	mAccelerometerAccumulator[0] = 0;
		        	mAccelerometerAccumulator[1] = 0;
		        	mAccelerometerAccumulator[2] = 0;
		    	}
	    	}
	    	
	   		// ------------------------------
	    	// Orientation
	    	// ------------------------------
	    	if (SharedPref.getBoolean(this, "orientation", true)) {
	        	if (mOrientationAccumulatorCount > 0) {
		        	ObjectNode inner = JsonNodeFactory.instance.objectNode();    	
					inner.put("Z", mOrientationAccumulator[2]/mOrientationAccumulatorCount);
					inner.put("Y", mOrientationAccumulator[1]/mOrientationAccumulatorCount);
					inner.put("X", mOrientationAccumulator[0]/mOrientationAccumulatorCount);
					dataNode.put("ORIENTATION", inner);				
	            	
	            	mOrientationAccumulatorCount = 0;     
	            	mOrientationAccumulator[0] = 0;
	            	mOrientationAccumulator[1] = 0;
	            	mOrientationAccumulator[2] = 0;
	        	}
	    	}
	    	
	    	
	   		// ------------------------------
	    	// Ambient light
	    	// ------------------------------		    
	    	if (SharedPref.getBoolean(this, "light", true)) {
	        	if (mLightAccumulatorCount > 0) {
		        	// Send data to output
	
		        	dataNode.put("LIGHT", mLightAccumulator / mLightAccumulatorCount);
	
			        mLightAccumulator = 0;
		   			mLightAccumulatorCount = 0;
			    }        		
	    	}
	   		// ------------------------------
	    	// Proximity
	    	// ------------------------------
	    	if (SharedPref.getBoolean(this, "proximity", true)) {
	        	if (mProximityAccumulatorCount > 0) {
	        		
					dataNode.put("PROXIMITY", mProximityAccumulator / mProximityAccumulatorCount);
	
			        mProximityAccumulator = 0;
		   			mProximityAccumulatorCount = 0;
			    }        		
	    	}
	    	
	   		// ------------------------------
        	// Battery Level
	   		// ------------------------------
	    	if (SharedPref.getBoolean(this, "battery", true)) {
	        	ObjectNode inner = JsonNodeFactory.instance.objectNode();    	
				inner.put("LEVEL", mBatteryLevel);
				inner.put("STATUS", mBatteryStatus);
				dataNode.put("BATTERY", inner);
	    	}

			// ------------------------------
		    // Backlight Status
	   		// ------------------------------
	    	if (SharedPref.getBoolean(this, "screen", true)) {
		   		PowerManager pm = (PowerManager) getSystemService(Context.POWER_SERVICE);	   		
		   		boolean screenOn = pm.isScreenOn();
		   		
				dataNode.put("SCREEN", screenOn ? 1:0);
	    	}
	    	
	   		// ------------------------------
	   		// Phone type
	   		// ------------------------------
	    	if (SharedPref.getBoolean(this, "model", true)) {
	//	   		String phoneManufacturer = Build.MANUFACTURER;
		   		String phoneModel = Build.MODEL;
				dataNode.put("MODEL", phoneModel);
	    	}
	   		
	   		// ------------------------------
	   		// Phone type
	   		// ------------------------------
	    	if (SharedPref.getBoolean(this, "locale", true)) {
		   		Configuration config = getResources().getConfiguration();	
		   		Locale locale = config.locale;
		   		String country = locale.getDisplayCountry();
		   		String language = locale.getDisplayLanguage();
	
		   		ObjectNode inner = JsonNodeFactory.instance.objectNode();    	
				inner.put("LANGUAGE", language);
				inner.put("COUNTRY", country);
				dataNode.put("LOCALE", inner);
	    	}	   		
	   		// ------------------------------
	   		// Telephony parameters
	   		// ------------------------------
	    	if (SharedPref.getBoolean(this, "telephony", true)) {
				mTelephonyManager = (TelephonyManager) this.getSystemService(Context.TELEPHONY_SERVICE);
		   		String myNumber = mTelephonyManager.getLine1Number();
		   		String setworkOperator = mTelephonyManager.getNetworkOperator();
	
		   		// TODO: Cell location needs some (a lot of!) work
		   		int cellId = -1;
		   		
		   		try {
					int type = mTelephonyManager.getPhoneType();
					if (type == TelephonyManager.PHONE_TYPE_CDMA) {
						CdmaCellLocation cdmaCellLocation = (CdmaCellLocation) mTelephonyManager.getCellLocation() ;
						if (cdmaCellLocation != null) {
							cellId = cdmaCellLocation.getBaseStationId();
						}
					}
					else {
						GsmCellLocation gsmCellLocation = (GsmCellLocation) mTelephonyManager.getCellLocation() ;
						if (gsmCellLocation != null) {
							cellId = gsmCellLocation.getCid();
						}
					}
				} catch (Exception e) {
					e.printStackTrace();
				}
		   		int networkType = mTelephonyManager.getPhoneType();		// For cell tower
		   		
		   		try {
					ObjectNode inner = JsonNodeFactory.instance.objectNode();    	
					inner.put("CELLID", cellId);
//				inner.put("MDN", myNumber);
					inner.put("MDN", Long.parseLong(myNumber));
					inner.put("NETWORK", setworkOperator);
					dataNode.put("TELEPHONY", inner);
				} catch (NumberFormatException e) {
					// TODO Auto-generated catch block
					//e.printStackTrace();
				}
	    	}	   		
	    	
	   		// ------------------------------
	   		// Location parameters
	   		// ------------------------------
	    	if (SharedPref.getBoolean(this, "location", true)) {
	        	if (mLocationFix != null) {
	        		ObjectNode inner = JsonNodeFactory.instance.objectNode();    	
	    			inner.put("LON", mLocationFix.getLongitude());
	    			inner.put("LAT", mLocationFix.getLatitude());
	    			inner.put("SPEED", mLocationFix.getSpeed());
	    			inner.put("TIME", mLocationFix.getTime());
	    			dataNode.put("LOCATION", inner);
	        	}
	    	}

	   		// ------------------------------
	   		// Lock status
	   		// ------------------------------
	    	if (SharedPref.getBoolean(this, "keylocked", true)) {
	        	KeyguardManager keyguardManager = (KeyguardManager) this.getSystemService(Context.KEYGUARD_SERVICE);
	        	if (keyguardManager != null) {
	        		boolean locked = keyguardManager.inKeyguardRestrictedInputMode();
	    			dataNode.put("KEYLOCKED", locked ? 1:0);        		
	        	}
	    	}        	

	    	// ------------------------------
	   		// Current Task(s)
	   		// ------------------------------
	    	if (SharedPref.getBoolean(this, "taskslist", true)) {
		    	try {
					ActivityManager activityManager = (ActivityManager) this.getSystemService(Context.ACTIVITY_SERVICE);
					List<ActivityManager.RunningTaskInfo> listTasks = activityManager.getRunningTasks(10);
		//				List<ActivityManager.RunningAppProcessInfo> listProcesses = activityManager.getRunningAppProcesses();
		//				List<ActivityManager.RunningServiceInfo> listServices = activityManager.getRunningServices(10);

					ArrayNode arraryNode = JsonNodeFactory.instance.arrayNode();				
					
					String tasks = "";
					for (int i = 0; i < listTasks.size(); i++) {
		//					Log.e(TAG, "Task: " + listTasks.get(i).baseActivity.getPackageName());
						tasks += listTasks.get(i).baseActivity.getPackageName() + ", ";
						arraryNode.add(listTasks.get(i).baseActivity.getPackageName());
					}
					if (listTasks.size() > 0) {
						ObjectNode outer = JsonNodeFactory.instance.objectNode(); 	        	
//						outer.put("TASKS", tasks);
						outer.put("TASKS", arraryNode);
//						dataNode.put("TASKS", tasks);        		
						dataNode.put("TASKS", arraryNode);        		
					}
		
					//				for (int i = 0; i < listProcesses.size(); i++) {
		//					Log.e(TAG, "" +	"Process: " + listProcesses.get(i).processName);
		//				}
		//				for (int i = 0; i < listServices.size(); i++) {
		//					Log.e(TAG, "Service: " + listServices.get(i).service);
		//				}
				} catch (SecurityException e) {
					Log.e(TAG, e.toString());
					e.printStackTrace();
				}
	    	}
	   		// ------------------------------
	   		// Bluetooth (enabled, list of paired devices)
	   		// ------------------------------
	    	if (SharedPref.getBoolean(this, "bluetooth", true)) {
				Boolean bluetoothEnabled = false;
				String btPairedDevices = "";
				
				
				ArrayNode arraryNode = JsonNodeFactory.instance.arrayNode();				
				
			    // First see if bluetooth is enabled
				BluetoothAdapter mBluetoothAdapter = BluetoothAdapter.getDefaultAdapter();
				if (mBluetoothAdapter != null) {
				    if (mBluetoothAdapter.isEnabled()) {
				    	bluetoothEnabled = true;				    	
				    }
					Set deviceBondedDevices = BluetoothAdapter.getDefaultAdapter().getBondedDevices();	
					Iterator bit = deviceBondedDevices.iterator();
					while(bit.hasNext())
					{
						BluetoothDevice bt = (BluetoothDevice) bit.next();
						if (bt != null) {
							btPairedDevices += bt.getName() + ", ";
							arraryNode.add(bt.getName());
						}
					}

					ObjectNode inner = JsonNodeFactory.instance.objectNode();    	
					inner.put("ENABLED", bluetoothEnabled ? 1:0);			
					if (bluetoothEnabled) {
//						inner.put("PAIREDDEVICES", btPairedDevices);
						inner.put("PAIREDDEVICES", arraryNode);
					}
					dataNode.put("BLUETOOTH", inner);					    
				} 
	    	}			
			
	   		// ------------------------------
	   		// Wifi 
	   		// ------------------------------
	    	if (SharedPref.getBoolean(this, "wifi", true)) {
				Boolean wifiEnabled = false;
				String accessPoints = "";			
				String connectedAccessPoint = "";
			
				ArrayNode arraryNode = JsonNodeFactory.instance.arrayNode();				
				WifiManager wifiManager = (WifiManager)getSystemService(Context.WIFI_SERVICE);
				if (wifiManager != null) {
					wifiEnabled = wifiManager.isWifiEnabled();
					
					List<ScanResult> list = wifiManager.getScanResults();	
					if (list != null) {
						for (ScanResult ap: list) {
							accessPoints += ap.SSID + ", ";
							arraryNode.add(ap.SSID);							
						}
					}
					
					WifiInfo wifiInfo = wifiManager.getConnectionInfo();
					if (wifiInfo != null) {
						connectedAccessPoint = wifiInfo.getSSID();
					}
	
					ObjectNode inner = JsonNodeFactory.instance.objectNode();    	
					inner.put("ENABLED", wifiEnabled ? 1:0);			
					
					if (wifiEnabled) {
//						inner.put("APSCAN", accessPoints);			
						inner.put("APSCAN", arraryNode);			
						inner.put("CONNECTED_AP", connectedAccessPoint);			
					}
					dataNode.put("WIFI", inner);			
				}
	    	}			
	    	
	    	
        	// If a phone call has been made then report it.
	    	if (SharedPref.getBoolean(this, "phonecall", true)) {
				if (mCurrentPhoneCall != null) {
					ObjectNode inner = JsonNodeFactory.instance.objectNode();    	
	    			inner.put("DIR", mCurrentPhoneCall.mDirection);
	    			inner.put("REMOTENUM", mCurrentPhoneCall.mRemoteNumber);
	    			inner.put("DURATION", mCurrentPhoneCall.mDuration);
	    			dataNode.put("PHONECALL", inner);        	
	        	
	        		mCurrentPhoneCall = null;
	        	}
	    	}	
	    	
	    	// If a message has been made then report it.
	    	if (SharedPref.getBoolean(this, "smsmessage", true)) {
	    		if (currentSMSMessage != null) {
					ObjectNode inner = JsonNodeFactory.instance.objectNode();    	
	    			inner.put("DIR", currentSMSMessage.mDirection);
	    			inner.put("REMOTENUM", currentSMSMessage.mRemoteNumber);
	    			inner.put("LENGTH", currentSMSMessage.mLength);
	    			dataNode.put("SMSMESSAGE", inner);        	
	    			currentSMSMessage = null;
	    		}
	    	}
	    	if (SharedPref.getBoolean(this, "mmsmessage", true)) {
	    		if (currentMMSMessage != null) {
					ObjectNode inner = JsonNodeFactory.instance.objectNode();    	
	    			inner.put("DIR", currentMMSMessage.mDirection);
	    			inner.put("REMOTENUM", currentMMSMessage.mRemoteNumber);
	    			inner.put("LENGTH", currentMMSMessage.mLength);
	    			dataNode.put("MMSMESSAGE", inner);        	
	    			currentMMSMessage = null;
	    		}
	    	}
	    	if (SharedPref.getBoolean(this, "webpage", true)) {
	    		if (currentUrl != null) {
	    			dataNode.put("WEBPAGE", currentUrl);	    			
	    			currentUrl = null;
	    		}
	    	}

	    	
	    	
	    	
	    	// ----------------------------------------------------
			// Send data to output
			// ----------------------------------------------------
        	mDataOutHandler.handleDataOut(dataNode);	
        	
			// Send the sample to the activity for it to display
	        ObjectNode item1 = JsonNodeFactory.instance.objectNode();
			item1.put("data", dataNode);
			Intent intent = new Intent();
    		intent.setAction(Constants.ACTION_STATUS_BROADCAST);
    		intent.putExtra("message", item1.toString());
   			sendBroadcast(intent);	        
		    
   			// Used to determine if we should continue sampling or wait for the next polling period
   			if (mMaxTotalAcceleration > mAccelerationThreshold) {
   				Log.e(TAG, "activity Detected");
   				mActivityDetected = true;
   			}
   			mMaxTotalAcceleration = 0;   			
   			
	    } // End synchronized (this) {		
	} // End sampleParameters()
	
	/**
	 * Receives broadcast notifications of all battery status events
	 */
	private BroadcastReceiver batteryInfoReceiver = new BroadcastReceiver() {
		@Override
		public void onReceive(Context context, Intent intent) {
			mBatteryLevel = intent.getIntExtra(BatteryManager.EXTRA_LEVEL,0); 
			mBatteryStatus = intent.getIntExtra(BatteryManager.EXTRA_STATUS,0); 
		}
	};

	/**
	 * Receives broadcast notifications of all telephone call events
	 */
	private BroadcastReceiver callReceiver = new BroadcastReceiver() {
		@Override
		public void onReceive(Context context, Intent intent) {
			int action = PhoneCall.T2_STATE_IDLE;
			
			if(intent.getAction().equals("android.intent.action.NEW_OUTGOING_CALL")) {
	            Bundle bundle = intent.getExtras();
	            
	            if(null == bundle)
	                    return;
	            
	            String phonenumber = intent.getStringExtra(Intent.EXTRA_PHONE_NUMBER);	
	        	mCurrentPhoneCall = new PhoneCall();

	            mCurrentPhoneCall.mRemoteNumber = phonenumber;

                //Log.e(TAG,"Outbound call - number: " + phonenumber);
                //Log.e(TAG,bundle.toString());
            	mCurrentPhoneCall.mStartTime = System.currentTimeMillis();
            	mCurrentPhoneCall.mDirection = "OUT";
            	action = PhoneCall.T2_STATE_OUTBOUND;
            	mCurrentPhoneCallState = action;
            	
			}
			else if (intent.getAction().equals("android.intent.action.PHONE_STATE")) {
		           Bundle bundle = intent.getExtras();
	                
	                if(null == bundle)
	                        return;
	                
	                String state = bundle.getString(TelephonyManager.EXTRA_STATE);	
	                if(state.equalsIgnoreCase(TelephonyManager.EXTRA_STATE_RINGING)) {
	                	action = PhoneCall.T2_STATE_RINGING;
	    	        	mCurrentPhoneCall = new PhoneCall();
                        String phonenumber = bundle.getString(TelephonyManager.EXTRA_INCOMING_NUMBER);
                        mCurrentPhoneCall.mRemoteNumber = phonenumber;
                        Log.e(TAG,"State = RINGING, Incomng Number: " + phonenumber);
	                }	                
	                if(state.equalsIgnoreCase(TelephonyManager.EXTRA_STATE_OFFHOOK)) {
	                	action = PhoneCall.T2_STATE_OFFHOOK;
                        Log.e(TAG,"State = OFFHOOK");
                        if (mCurrentPhoneCallState == PhoneCall.T2_STATE_RINGING) {
                        	// Inbound call started 
                        	if (mCurrentPhoneCall != null) {		// Should be ok but make sure
                            	mCurrentPhoneCall.mStartTime = System.currentTimeMillis();
                            	mCurrentPhoneCall.mDirection = "IN";
                        	}
                        }
	                }	                
	                if(state.equalsIgnoreCase(TelephonyManager.EXTRA_STATE_IDLE)) {
	                	action = PhoneCall.T2_STATE_IDLE;
                        Log.e(TAG,"State = IDLE");
                        
                        if (mCurrentPhoneCallState == PhoneCall.T2_STATE_OFFHOOK) {
                        	if (mCurrentPhoneCall != null) {		// Should be ok but make sure
                            	// Call has been completed, trigger writing of parameters
                            	mCurrentPhoneCall.mDuration = (int) (System.currentTimeMillis() - mCurrentPhoneCall.mStartTime)/1000;
                            	
		                        AsyncTask<Integer, Void, Void> asyncTask = new AsyncTask<Integer, Void, Void>() {
		                            	
			        				@Override
			        				protected Void doInBackground(Integer... integers) {
		                            	Log.e(TAG, String.format("**Background ** Call Completed: Dir= %s, Remote Party = %s, Duration = %d seconds",
		                            			mCurrentPhoneCall.mDirection, mCurrentPhoneCall.mRemoteNumber, mCurrentPhoneCall.mDuration)); 
		           					try {
										sampleParameters();
									} catch (Exception e) {
										Log.e(TAG, e.toString());
										e.printStackTrace();
									}	        					
			        					
			        					return null;
			        				}
			        	
			        				@Override
			        				protected void onPostExecute(Void aVoid) {
			        				}
			        			};
		                            	
		               			asyncTask.execute(0, 0);                            	
                        	}
                        }
                        else {
            	        	mCurrentPhoneCall = null;;
                        }
                        
	                }	                
	                mCurrentPhoneCallState = action;			
			}
		}
	};

	/**
	 * Receives broadcast notifications of all SMS message events
	 * This is also supposed to work for MMS but it doesn't
	 */
	private BroadcastReceiver messageReceiver = new BroadcastReceiver() {
		@Override
		public void onReceive(Context context, Intent intent) {
			if(intent.getAction().equals("android.provider.Telephony.SMS_RECEIVED")) {
	            Bundle bundle = intent.getExtras();
	            
	            if(null == bundle)
	                    return;
	            
	    		Object messages[] = (Object[]) bundle.get("pdus");
	    		SmsMessage smsMessage[] = new SmsMessage[messages.length];
	    		for (int n = 0; n < messages.length; n++) {
	    			smsMessage[n] = SmsMessage.createFromPdu((byte[]) messages[n]);
	    		}
	    		Log.e(TAG, "message received: " + smsMessage[0].getMessageBody());
	    		Log.e(TAG, "from: " + smsMessage[0].getOriginatingAddress());
	    		Log.e(TAG, "stop");

			}
			else if(intent.getAction().equals("android.provider.Telephony.WAP_PUSH_RECEIVED")) {
	            Bundle bundle = intent.getExtras();
	            
	            if(null == bundle)
	                    return;
	            
	    		Object messages[] = (Object[]) bundle.get("pdus");
	    		SmsMessage smsMessage[] = new SmsMessage[messages.length];
	    		for (int n = 0; n < messages.length; n++) {
	    			smsMessage[n] = SmsMessage.createFromPdu((byte[]) messages[n]);
	    		}
	    		Log.e(TAG, "message received: " + smsMessage[0].getMessageBody());
	    		Log.e(TAG, "from: " + smsMessage[0].getOriginatingAddress());
	    		Log.e(TAG, "stop");

			}
		};
	};

	@Override
	public void onLocationChanged(Location location) {
        if (location != null) {
//        	Log.e(TAG, String.format("{LAT:%f, LON:%f, TIME:%d", location.getLatitude(), location.getLongitude(), location.getTime()));
            mLocationFix = location;            
        }
	}

	@Override
	public void onProviderDisabled(String provider) {
		// TODO Auto-generated method stub
	}

	@Override
	public void onProviderEnabled(String provider) {
		// TODO Auto-generated method stub
	}

	@Override
	public void onStatusChanged(String provider, int status, Bundle extras) {
		// TODO Auto-generated method stub
	}

	/* (non-Javadoc)
	 * @see com.t2.bigbrother.Receiver.OnBioFeedbackMessageRecievedListener#onReceived(java.lang.String)
	 * 
	 * Command message received from the main activity
	 */
	@Override
	public void onReceived(String message) {
        boolean mSamplingEnabled = SharedPref.getBoolean(this, "sampling_enabled", false);
        Log.d(TAG, "sampling_enabled = " + mSamplingEnabled);
        
        if (message != null) {
            try {
    			if (message.equalsIgnoreCase(Constants.SERVICE_OFF) && mContinousService) {
    				// Tell the service to stop after it detects no activity
    				mContinousService = false;
    				mSamplingActive = true;    	
    		        mAbortService = true;    	
    				
    			}
    		} catch (Exception e) {
    	        Log.e(TAG, "Exception = " + e.toString());
    			e.printStackTrace();
    		} // End catch (Excepion
        }
	}	

    /**
     * @author scott.coleman
     * 
     * Receives messages events any time a SMS or MMS is sent or received 
     *
     */
    private class SMSObserver extends ContentObserver {

        int count = 0;
        String lastMessage = null;

        public SMSObserver(Handler handler) {
            super(handler);
        }

        public void onChange(boolean selfChange) {
            super.onChange(selfChange);

            //Log.e("SMSTEST", "HIT ON CHANGE");

            Uri uriSMSURI = Uri.parse("content://sms");
//            Uri uriSMSURI = Uri.parse("content://mms");
            Cursor cur = getContentResolver().query(uriSMSURI, null, null,
                         null, null);
            String[] columns = cur.getColumnNames();
            count = cur.getCount();
            cur.moveToNext();
            
            String address;
            String content;
            String direction;
            String date;            
            
            // Figure out if mms or SMS - mms has 32 headers, sms has 17
            if (columns.length == 32) {
            	// MMS
                date = cur.getString(cur.getColumnIndex("date"));
                content = cur.getString(cur.getColumnIndex("sub"));            
                int dir = cur.getInt(cur.getColumnIndex("m_type"));
                if (dir == 128) {
                	direction = "OUT";
                	Log.e("SMSTEST", "Inbound MMS =>> date = " + date + ", content = " + content);                	
                }
                else {
                	direction = "IN";
                	Log.e("SMSTEST", "Inbound MMS =>> date = " + date + ", content = " + content);                	
                }
            }
            else if (columns.length == 17) {
            	// SMS
                address = cur.getString(cur.getColumnIndex("address"));
                content = cur.getString(cur.getColumnIndex("body"));            
                String protocol = cur.getString(cur.getColumnIndex("protocol"));
            	int type = cur.getInt(cur.getColumnIndex("type"));
            	String id = cur.getString(cur.getColumnIndex("_id"));            	
            	date = cur.getString(cur.getColumnIndex("date"));            	
                String aMd5 = md5(date + content);
                
                if(protocol == null) {
                	
                    count++;
                    //Log.e("SMSTEST", "SMS SENT: count: " + count);

                    if (aMd5 != null) {
                        //Log.e("SMSTEST", "md5 = " + aMd5);
                        
                        // We need to use the MD5 of the message because this routine gets 
                    	// called multiple times for every message that is sent.
                    	// This way we only record the message one time 
                    	// (when the MD5 is new)
                    	if (!mLastSentSMSMd5.equalsIgnoreCase(aMd5)) {
                        	mLastSentSMSMd5 = aMd5;
                        	currentSMSMessage = new TextMessage();
                        	currentSMSMessage.mType = "SMS";
                        	currentSMSMessage.mDirection = "OUT";
                        	currentSMSMessage.mLength = content.length();
                        	currentSMSMessage.mRemoteNumber = address;
                        	RecordNewMessage();
                        }
                    }
                }else{
                	currentSMSMessage = new TextMessage();
                	currentSMSMessage.mType = "SMS";
                	currentSMSMessage.mDirection = "IN";
                	currentSMSMessage.mLength = content.length();
                	currentSMSMessage.mRemoteNumber = address;
                	RecordNewMessage();
                }            	
            }
        }
    }    
 
    /**
     * @author scott.coleman
     * 
     * Observes browser. If change in current URL is detected, it then logs the new URL
     *
     */
    private class T2BrowserObserver extends ContentObserver {

        int count = 0;
        String lastMessage = null;

        public T2BrowserObserver(Handler handler) {
            super(handler);
        }

        public void onChange(boolean selfChange) {
            super.onChange(selfChange);

            try {
				Cursor cur = getContentResolver().query(Browser.BOOKMARKS_URI,Browser.HISTORY_PROJECTION, null, null, null);
				String[] columns = cur.getColumnNames();
				count = cur.getCount();
				cur.moveToFirst();
				cur.moveToPosition(count - 1);
				String url = cur.getString(cur.getColumnIndex("url"));
				
				if (!mLastBrowserUrl.equalsIgnoreCase(url)) {
					mLastBrowserUrl = url;
					currentUrl = url;
					Log.e("test", count - 1 + " - " + url);
					RecordNewBrowserUrl();					
				}
				
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
        }    
    }
    
    
    
    
    /**
     * Causes sampleParameters() to run in the background.
     * This will record any new  currentSMSMessage or currentMMSMessage to the data out handler
     */
    void RecordNewMessage() {
        AsyncTask<Integer, Void, Void> asyncTask = new AsyncTask<Integer, Void, Void>() {
        	
			@Override
			protected Void doInBackground(Integer... integers) {

				if (currentSMSMessage != null) {
					Log.e(TAG, String.format("**Background ** SMS Message Detected: Dir= %s, Remote Party = %s, Length = %d bytes",
							currentSMSMessage.mDirection, currentSMSMessage.mRemoteNumber, currentSMSMessage.mLength)); 
				}
				try {
				sampleParameters();
			} catch (Exception e) {
				Log.e(TAG, e.toString());
				e.printStackTrace();
			}	        					
				
				return null;
			}

			@Override
			protected void onPostExecute(Void aVoid) {
			}
		};
            	
			asyncTask.execute(0, 0);                            	
    	
    }
    
    /**
     * Causes sampleParameters() to run in the background.
     * This will record any new  mLastBrowserUrl to the data out handler
     */
    void RecordNewBrowserUrl() {
        AsyncTask<Integer, Void, Void> asyncTask = new AsyncTask<Integer, Void, Void>() {
        	
			@Override
			protected Void doInBackground(Integer... integers) {

				if (currentSMSMessage != null) {
					Log.e(TAG, String.format("**Background ** New URL browsed to: " + mLastBrowserUrl)); 
				}
				try {
				sampleParameters();
			} catch (Exception e) {
				Log.e(TAG, e.toString());
				e.printStackTrace();
			}	        					
				
				return null;
			}

			@Override
			protected void onPostExecute(Void aVoid) {
			}
		};
            	
			asyncTask.execute(0, 0);                            	
    	
    }
    
    /**
     * Calculates the MD5 digest of an input string
     * @param in
     * @return
     */
    private String md5(String in) {
        MessageDigest digest;
        try {
            digest = MessageDigest.getInstance("MD5");
            digest.reset();        
            digest.update(in.getBytes());
            byte[] a = digest.digest();
            int len = a.length;
            StringBuilder sb = new StringBuilder(len << 1);
            for (int i = 0; i < len; i++) {
                sb.append(Character.forDigit((a[i] & 0xf0) >> 4, 16));
                sb.append(Character.forDigit(a[i] & 0x0f, 16));
            }
            return sb.toString();
        } catch (NoSuchAlgorithmException e) { e.printStackTrace(); }
        return null;
    } 
}